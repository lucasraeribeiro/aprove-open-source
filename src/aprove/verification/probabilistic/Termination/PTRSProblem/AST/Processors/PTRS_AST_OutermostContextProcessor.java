package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import java.util.*;

import org.apache.commons.math3.fraction.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Probabilistic adaptations of the context transformations T2 and T3 in
 * Raffelsieper and Zantema, "A transformational approach to prove outermost
 * termination automatically", Definitions 4.2 and 4.5.
 *
 * Full AST of the target implies outermost AST of the source: every outermost
 * ground step is a single target step with the same outcome probabilities.
 * For a step below the root, an anti-matching pattern covers its immediate
 * parent. T2 replaces that pattern's direct argument by a hole; T3 first
 * unifies the argument with the source lhs and retains the resulting guard.
 * Full target rewriting supplies the context above that parent. Extra target
 * steps are permitted, so the implication is SOUND, not EQUIVALENT.
 *
 * Quasi-left-linearity makes the root-redex language the union of the linear
 * lhs languages, allowing finite anti-matching and preserving root-redex
 * tests when source variables are grounded by one fresh constant.
 */
public class PTRS_AST_OutermostContextProcessor extends PTRS_AST_ProblemProcessor {

    public enum Transformation {
        // Bare T2 is already a processor name in AProVE's strategy namespace.
        CONTEXT_T2, CONTEXT_T3;

        @Override
        public String toString() {
            return this == CONTEXT_T2 ? "T2" : "T3";
        }
    }

    private final Transformation transformation;

    @ParamsViaArgumentObject
    public PTRS_AST_OutermostContextProcessor(final Arguments arguments) {
        this.transformation = Objects.requireNonNull(arguments.transformation);
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        if (Options.certifier != Certifier.NONE
            || ptrs.getTarget() != ProbabilisticTerminationResult.AST
            || ptrs.getRewriteStrategy() != RewriteStrategy.OUTERMOST) {
            return false;
        }

        // Every nonlinear lhs must be an instance of a linear source lhs.
        // It remains a firing rule; only anti-matching can ignore it.
        for (final ProbabilisticRule rule : ptrs.getPR()) {
            final TRSFunctionApplication lhs = rule.getLeft();
            if (!lhs.isLinear()) {
                boolean covered = false;
                for (final ProbabilisticRule other : ptrs.getRuleMap().get(lhs.getRootSymbol())) {
                    if (other.getLeft().isLinear() && other.getLeft().matches(lhs)) {
                        covered = true;
                        break;
                    }
                }
                if (!covered) {
                    return false;
                }
            }
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter)
        throws AbortionException {
        if (!isPTRSApplicable(ptrs)) {
            return ResultFactory.unsuccessful();
        }
        aborter.checkAbortion();

        final FreshNameGenerator names = new FreshNameGenerator(ptrs.getSignature(), FreshNameGenerator.APPEND_NUMBERS);
        final FunctionSymbol top = FunctionSymbol.create(names.getFreshName("top", false), 1);
        final FunctionSymbol ground = FunctionSymbol.create(names.getFreshName("outermost_var", false), 0);
        final Set<FunctionSymbol> signature = new LinkedHashSet<>(ptrs.getSignature());
        signature.add(ground);
        final List<TRSFunctionApplication> antiMatching = computeAntiMatching(ptrs, signature, aborter);
        final Set<ProbabilisticRule> rules = new LinkedHashSet<>();

        // Root steps: top(l) -> {p_j : top(r_j)}.
        for (final ProbabilisticRule rule : ptrs.getPR()) {
            aborter.checkAbortion();
            addContextRule(rules, Context.create(TRSTerm.createFunctionApplication(top, rule.getLeft()), Position.create(0)),
                rule, TRSSubstitution.create(), aborter);
        }

        for (final TRSFunctionApplication pattern : antiMatching) {
            for (final ProbabilisticRule rule : ptrs.getPR()) {
                aborter.checkAbortion();
                // Patterns and source rules must have disjoint variables for T3.
                final TRSFunctionApplication disjointPattern = (TRSFunctionApplication) pattern.renameVariables(rule.getLeft().getVariables());
                for (int i = 0; i < disjointPattern.getRootSymbol().getArity(); i++) {
                    aborter.checkAbortion();
                    final TRSSubstitution subst;
                    if (this.transformation == Transformation.CONTEXT_T3) {
                        subst = disjointPattern.getArguments().get(i).getMGU(rule.getLeft());
                        if (subst == null) {
                            continue;
                        }
                    } else {
                        subst = TRSSubstitution.create();
                    }
                    final Context context = Context.create(disjointPattern, Position.create(i));
                    addContextRule(rules, context, rule, subst, aborter);
                }
            }
        }

        // PTRSProblem derives its signature from its rules. Include the fresh
        // grounding constant even if it occurred only in zero-arity patterns.
        // This extra deterministic rule terminates and is irrelevant to the
        // simulation of source steps (the fresh constant is a source normal form).
        final TRSFunctionApplication groundTerm = TRSTerm.createFunctionApplication(ground);
        rules.add(ProbabilisticRule.create(TRSTerm.createFunctionApplication(top, groundTerm), groundTerm));

        // The paper's context transformations require full target rewriting.
        // top(t) is generally not a basic target term, so use all target terms.
        final PTRSProblem transformed = PTRSProblem.create(ImmutableCreator.create(rules),
            RewriteStrategy.FULL, ProbabilisticTerminationResult.AST, false);
        return ResultFactory.proved(transformed, YNMImplication.SOUND,
            new OutermostContextProof(this.transformation, top, ground, antiMatching.size(), rules.size()));
    }

    /** Apply the same context and substitution to the lhs and every outcome. */
    private static void addContextRule(final Set<ProbabilisticRule> rules, final Context context,
        final ProbabilisticRule rule, final TRSSubstitution subst, final Abortion aborter) throws AbortionException {
        final TRSFunctionApplication lhs = (TRSFunctionApplication) context.replace(rule.getLeft()).applySubstitution(subst);
        final HashMultiSet<Pair<TRSTerm, BigFraction>> outcomes = new HashMultiSet<>();
        for (final var entry : rule.getRight().getProbabilityMapping().entrySet()) {
            aborter.checkAbortion();
            final Pair<TRSTerm, BigFraction> outcome = entry.getKey();
            final TRSTerm rhs = context.replace(outcome.getKey()).applySubstitution(subst);
            // An MGU can identify outcomes. Add their multiplicities instead
            // of overwriting a previously inserted (term, probability) pair.
            outcomes.add(new Pair<>(rhs, outcome.getValue()), entry.getValue());
        }
        rules.add(ProbabilisticRule.create(lhs, new MultiDistribution<>(outcomes)));
    }

    // ================================================================================
    // Finite anti-matching for a union of linear patterns
    // ================================================================================

    private static List<TRSFunctionApplication> computeAntiMatching(final PTRSProblem ptrs,
        final Set<FunctionSymbol> signature, final Abortion aborter) throws AbortionException {
        final FreshVarGenerator variables = new FreshVarGenerator(ptrs.getVariables());
        List<TRSFunctionApplication> complement = new ArrayList<>();
        for (final FunctionSymbol f : signature) {
            aborter.checkAbortion();
            complement.add(skeleton(f, variables));
        }

        // Nonlinear lhss are covered by linear ones (checked in isPTRSApplicable).
        // Subtract each linear lhs language from the current cover of ground terms.
        for (final ProbabilisticRule rule : ptrs.getPR()) {
            aborter.checkAbortion();
            final TRSFunctionApplication lhs = rule.getLeft();
            if (lhs.isLinear()) {
                final List<TRSFunctionApplication> next = new ArrayList<>();
                for (final TRSFunctionApplication candidate : complement) {
                    subtract(candidate, lhs, signature, variables, next, aborter);
                }
                complement = next;
            }
        }

        // Keep a small cover by removing instances, including variable variants.
        final List<TRSFunctionApplication> minimal = new ArrayList<>();
        for (final TRSFunctionApplication candidate : complement) {
            aborter.checkAbortion();
            boolean covered = false;
            for (final TRSFunctionApplication other : minimal) {
                aborter.checkAbortion();
                if (other.matches(candidate)) {
                    covered = true;
                    break;
                }
            }
            if (!covered) {
                final Iterator<TRSFunctionApplication> iterator = minimal.iterator();
                while (iterator.hasNext()) {
                    aborter.checkAbortion();
                    if (candidate.matches(iterator.next())) {
                        iterator.remove();
                    }
                }
                minimal.add(candidate);
            }
        }
        return minimal;
    }

    /**
     * Partition a linear candidate at a variable below a nonvariable lhs position.
     * Each refinement fixes another lhs symbol, so subtraction is finite. A root
     * clash retains the candidate; a covering match discards it completely.
     */
    private static void subtract(final TRSFunctionApplication candidate, final TRSFunctionApplication lhs,
        final Set<FunctionSymbol> signature, final FreshVarGenerator variables,
        final List<TRSFunctionApplication> result, final Abortion aborter) throws AbortionException {
        aborter.checkAbortion();
        if (lhs.matches(candidate)) {
            return;
        }
        if (!lhs.unifies(candidate)) {
            result.add(candidate);
            return;
        }
        final Position split = findSplit(candidate, lhs, Position.EPSILON);
        if (split == null) {
            throw new IllegalStateException("Unifiable linear patterns without a covering match or a split position");
        }
        for (final FunctionSymbol f : signature) {
            aborter.checkAbortion();
            final TRSFunctionApplication refined = (TRSFunctionApplication) candidate.replaceAt(split, skeleton(f, variables));
            subtract(refined, lhs, signature, variables, result, aborter);
        }
    }

    private static Position findSplit(final TRSTerm candidate, final TRSTerm lhs, final Position position) {
        if (lhs.isVariable()) {
            return null;
        }
        if (candidate.isVariable()) {
            return position;
        }
        final List<TRSTerm> args = ((TRSFunctionApplication) candidate).getArguments();
        final List<TRSTerm> lhsArgs = ((TRSFunctionApplication) lhs).getArguments();
        for (int i = 0; i < args.size(); i++) {
            final Position split = findSplit(args.get(i), lhsArgs.get(i), position.append(i));
            if (split != null) {
                return split;
            }
        }
        return null;
    }

    private static TRSFunctionApplication skeleton(final FunctionSymbol f, final FreshVarGenerator variables) {
        final List<TRSTerm> args = new ArrayList<>(f.getArity());
        final TRSVariable x = TRSTerm.createVariable("x");
        for (int i = 0; i < f.getArity(); i++) {
            args.add(variables.getFreshVariable(x, false));
        }
        return TRSTerm.createFunctionApplication(f, args);
    }

    // ================================================================================
    // Proof and strategy arguments
    // ================================================================================

    public static class OutermostContextProof extends Proof.DefaultProof {

        private final Transformation transformation;
        private final FunctionSymbol top;
        private final FunctionSymbol ground;
        private final int patternCount;
        private final int ruleCount;

        private OutermostContextProof(final Transformation transformation, final FunctionSymbol top,
            final FunctionSymbol ground, final int patternCount, final int ruleCount) {
            this.transformation = transformation;
            this.top = top;
            this.ground = ground;
            this.patternCount = patternCount;
            this.ruleCount = ruleCount;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder proof = new StringBuilder();
            proof.append(o.export("Applied the probabilistic context transformation " + this.transformation
                + " based on Raffelsieper and Zantema, A transformational approach to prove outermost termination automatically, "
                + "Definition " + (this.transformation == Transformation.CONTEXT_T2 ? "4.2" : "4.5") + "."));
            proof.append(o.paragraph());
            proof.append(o.export("The source PTRS is quasi-left-linear. Computed " + this.patternCount
                + " anti-matching patterns and generated " + this.ruleCount + " rules. "
                + (this.transformation == Transformation.CONTEXT_T2
                    ? "Source rules are inserted into all direct-argument anti-matching contexts. "
                    : "Source rules are inserted only after unifying their lhs with the selected anti-matching argument; "
                        + "the same MGU is applied to the entire context and all outcomes. ")
                + "Probabilities and outcome multiplicities are retained."));
            proof.append(o.paragraph());
            proof.append(o.export("Source terms are encoded as " + this.top.getName() + "(t). "
                + "The fresh constant " + this.ground.getName() + " grounds source variables without enabling a new root redex. "
                + "Its deterministic wrapper-removal rule keeps this constant in the target signature. "
                + "Every grounded outermost source step is simulated by one full target step with the same probabilities. "
                + "Full AST of the target on all start terms therefore implies outermost AST of the source. "
                + "The transformation is sound and may introduce additional reductions."));
            return proof.toString();
        }
    }

    public static class Arguments {
        public Transformation transformation = Transformation.CONTEXT_T3;
    }
}

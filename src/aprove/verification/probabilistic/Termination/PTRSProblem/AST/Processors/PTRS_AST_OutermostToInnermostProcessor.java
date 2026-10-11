package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import java.util.*;

import org.apache.commons.math3.fraction.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Reduces outermost AST to innermost AST using the probabilistic marker
 * transformation of Definition 3.1.1 (rules T1--T6) in the thesis.
 * Administrative rules are deterministic; T3 preserves the source
 * multi-distribution, including the multiplicities of its entries.
 */
public class PTRS_AST_OutermostToInnermostProcessor extends PTRS_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        return Options.certifier == Certifier.NONE
            && ptrs.getTarget() == ProbabilisticTerminationResult.AST
            && ptrs.getRewriteStrategy() == RewriteStrategy.OUTERMOST;
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
        final FunctionSymbol top = freshSymbol(names, "top", 1);
        final FunctionSymbol reduce = freshSymbol(names, "reduce", 1);
        final FunctionSymbol goUp = freshSymbol(names, "go_up", 1);
        final FunctionSymbol result = freshSymbol(names, "result", 1);
        final Map<FunctionSymbol, FunctionSymbol> redexSymbols = new LinkedHashMap<>();
        final Set<ProbabilisticRule> rules = new LinkedHashSet<>();
        final TRSVariable x = TRSTerm.createVariable("x");

        // Include every source symbol, including constructors and constants.
        for (final FunctionSymbol f : ptrs.getSignature()) {
            aborter.checkAbortion();
            final int arity = f.getArity();
            final FunctionSymbol check = freshSymbol(names, "check_" + f.getName(), 1);
            final FunctionSymbol redex = freshSymbol(names, "redex_" + f.getName(), arity);
            redexSymbols.put(f, redex);
            final List<TRSTerm> args = new ArrayList<>(arity);
            for (int i = 0; i < arity; i++) {
                args.add(TRSTerm.createVariable("x" + (i + 1)));
            }
            final TRSFunctionApplication sourceTerm = TRSTerm.createFunctionApplication(f, args);
            final TRSFunctionApplication checkedRedex =
                TRSTerm.createFunctionApplication(check, TRSTerm.createFunctionApplication(redex, args));

            // T1: start the root-redex test.
            rules.add(ProbabilisticRule.create(TRSTerm.createFunctionApplication(reduce, sourceTerm), checkedRedex));

            // T4: a source rule has fired; start returning to the root.
            rules.add(ProbabilisticRule.create(
                TRSTerm.createFunctionApplication(check, TRSTerm.createFunctionApplication(result, x)),
                TRSTerm.createFunctionApplication(goUp, x)));

            for (int i = 0; i < arity; i++) {
                aborter.checkAbortion();
                final FunctionSymbol in = freshSymbol(names, "in_" + f.getName() + "_" + (i + 1), arity);
                final List<TRSTerm> downArgs = new ArrayList<>(args);
                downArgs.set(i, TRSTerm.createFunctionApplication(reduce, args.get(i)));

                // T2: innermost evaluation permits descent only if redex is normal.
                rules.add(ProbabilisticRule.create(checkedRedex, TRSTerm.createFunctionApplication(in, downArgs)));

                // T5: restore the source context and move the return marker up.
                final List<TRSTerm> upArgs = new ArrayList<>(args);
                upArgs.set(i, TRSTerm.createFunctionApplication(goUp, args.get(i)));
                rules.add(ProbabilisticRule.create(TRSTerm.createFunctionApplication(in, upArgs),
                    TRSTerm.createFunctionApplication(goUp, sourceTerm)));
            }
        }

        // T3: replace only the source lhs root and wrap each outcome in result.
        // Do not flatten the multi-distribution to its support.
        for (final ProbabilisticRule rule : ptrs.getPR()) {
            aborter.checkAbortion();
            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSFunctionApplication newLhs =
                TRSTerm.createFunctionApplication(redexSymbols.get(lhs.getRootSymbol()), lhs.getArguments());
            final HashMultiSet<Pair<TRSTerm, BigFraction>> outcomes = new HashMultiSet<>();
            for (final var entry : rule.getRight().getProbabilityMapping().entrySet()) {
                aborter.checkAbortion();
                final Pair<TRSTerm, BigFraction> outcome = entry.getKey();
                outcomes.put(new Pair<>(TRSTerm.createFunctionApplication(result, outcome.getKey()), outcome.getValue()),
                    entry.getValue());
            }
            rules.add(ProbabilisticRule.create(newLhs, new MultiDistribution<>(outcomes)));
        }

        // T6: reset at the root for the next simulated source step.
        rules.add(ProbabilisticRule.create(
            TRSTerm.createFunctionApplication(top, TRSTerm.createFunctionApplication(goUp, x)),
            TRSTerm.createFunctionApplication(top, TRSTerm.createFunctionApplication(reduce, x))));

        // enc(t) = top(reduce(t)) is not a basic term of the transformed PTRS.
        // Proving AST for all target terms also covers basic source start terms.
        final PTRSProblem transformed = PTRSProblem.create(ImmutableCreator.create(rules),
            RewriteStrategy.INNERMOST, ProbabilisticTerminationResult.AST, false);
        return ResultFactory.proved(transformed, YNMImplication.SOUND, new OutermostToInnermostProof(top, reduce));
    }

    private static FunctionSymbol freshSymbol(final FreshNameGenerator names, final String name, final int arity) {
        return FunctionSymbol.create(names.getFreshName(name, false), arity);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class OutermostToInnermostProof extends Proof.DefaultProof {

        private final FunctionSymbol top;
        private final FunctionSymbol reduce;

        private OutermostToInnermostProof(final FunctionSymbol top, final FunctionSymbol reduce) {
            this.top = top;
            this.reduce = reduce;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder proof = new StringBuilder();
            proof.append(o.export("Applied the probabilistic outermost-to-innermost marker transformation (T1--T6)."));
            proof.append(o.paragraph());
            proof.append(o.export("Source terms are encoded as " + this.top.getName() + "(" + this.reduce.getName()
                + "(t)). Each outermost source step is simulated by a finite, non-empty innermost derivation. "
                + "The firing rules preserve all source probabilities and multiplicities; "
                + "all administrative rules have probability 1. Innermost rewriting prevents descent below a source redex."));
            proof.append(o.paragraph());
            proof.append(o.export("If the transformed PTRS is innermost AST on all terms, "
                + "then the original PTRS is outermost AST. The generated obligation uses all start terms "
                + "because the encoded source terms are not basic target terms."));
            return proof.toString();
        }
    }
}

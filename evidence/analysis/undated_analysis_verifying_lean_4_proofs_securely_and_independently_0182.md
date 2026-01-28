# Verifying Lean 4 Proofs Securely and Independently
*Converted from: Verifying Lean 4 Proofs Securely and Independently.docx*
---

# Verifying Lean 4 Proofs Securely and Independently

## Lean’s Own Verification and Termination Checks

Lean 4’s built-in type checker and kernel are the primary tools to verify proofs. When you run Lean on your code (for example, via lake build or the VS Code extension), it will type-check every definition and proof. Lean’s trusted kernel guarantees that any proof which passes this check is logically correct[1][2]. In practice, this means if the AI-generated proofs type-check with no errors or warnings, Lean has formally verified them as correct relative to your axioms and definitions. Lean automatically checks termination and totality of functions as well. All functions must either obviously terminate or use a well-founded measure; otherwise you must mark them partial/unsafe (which you should avoid in proofs)[3]. This ensures that recursive definitions (like those using multiset orders or ordinals) truly are terminating, barring any explicit override.

When using Lean locally, no data is sent externally, so your sensitive theory remains private. It’s wise to disable any network features or telemetry in your editor and avoid external dependencies. By default, Lean does not upload code anywhere – the checking is done on your machine. Lean will also flag incomplete proofs: if an AI introduced a sorry (an unfinished proof), Lean emits a warning (“declaration uses ‘sorry’”) and treats it as an axiom. You can detect these by searching for sorry in your code or using #print axioms on a theorem to see if sorryAx appears[4]. In short, simply running Lean on the project is the first and most important verification step – it confirms all proofs, ensures termination, and will alert you to any unsound steps. Keep in mind, however, that Lean verifies correctness with respect to the formal statements you provided; it cannot tell if the formal theorem truly captures your intended theory – that gap is something only a careful human review can bridge[5].

## Isolated Continuous Integration (CI) and Build Environments

To continually verify proofs without exposing your code, you can set up a local or offline CI pipeline. For example, you might run a Jenkins server or a GitLab CI runner on a machine under your control (no public cloud) that builds your Lean project on each change. This ensures that any errors introduced by edits or AI suggestions are caught immediately, in a controlled environment. Using a containerization approach is highly effective here: you can run Lean in a Docker container with no internet access. The Lean community provides Docker images (e.g. leanprovercommunity/lean4) that contain Lean 4 and its tools. By using such an image, you can mount your project into the container and run the build – all proofs will be checked inside the sandbox. This setup guarantees privacy because your code never leaves the container, and the container itself can be run on an offline machine[6]. For instance, you could create a Docker container that runs lake build on your project; if the build fails (due to a broken proof or non-termination), the container exits with an error, alerting you to a problem.

Using VS Code offline: If you prefer an interactive environment, you can install Lean and VS Code on an air-gapped computer or use VS Code’s remote containers extension to work inside a locally-hosted Docker container. This way, all the Lean checking (which happens in the Lean server) stays local. No code or proof obligations will be sent to any cloud service. Ensure features like mathlib’s online oleans cache are disabled or pointed to a local source to avoid any external fetch. In an offline CI setup, you should also avoid posting build logs to public sites since they might contain parts of your code. Keep the CI logs and artifacts on internal servers.

Self-hosted runners: If you use a service like GitHub or GitLab, configure a self-hosted runner on your own machine. That runner can perform the Lean build without sending data to the cloud. The key is that the code repository should be private (or on an internal version control system), and the runner should not expose logs publicly. By combining these practices, you get the benefits of automated proof checking and regression testing, while fully maintaining privacy. In summary, an isolated CI or build environment continuously validates your Lean proofs and build, catching errors early, all without exposing your proprietary theory.

## Lean Code Auditing Tools (Axioms, Unsafe Code, and Incompleteness)

Beyond basic type checking, Lean provides some audit tools to help ensure there are no hidden flaws in the proofs:

- Axiom usage checks: Lean’s #print axioms command is extremely useful for auditing proofs. It lists any axioms a given theorem or definition relies on. In your context, “axioms” include things like classical logic principles, choice, or any sorry usages. After an AI generates a proof, run #print axioms on the key theorems. Ideally, you want to see “does not depend on any axioms” for most of them. For example, Lean might show:

#print axioms def1 -- depends on axioms: [propext, Classical.choice, Quot.sound]  
#print axioms def2 -- does not depend on any axioms[7]

In this sample (from Lean’s documentation), def1 was using some classical axioms (propositional extensionality, choice, etc.), whereas def2 was completely axiom-free. If your AI-generated proofs inadvertently pulled in something like the axiom of choice or a classical law that you want to avoid (for instance, if you intend a constructive development), this will be revealed here. Crucially, if any proof depends on sorryAx, it means an incomplete proof (a sorry) slipped through[4]. In a secure verification workflow, you might even write a script to scan the output of #print axioms for each definition/theorem and flag any occurrence of undesirable axioms or sorryAx.

- Unsafe code and partial functions: Since Lean ensures termination and totality, any use of unsafe functions or partial def is a red flag. Audit your code (manually or with grep) for the keywords unsafe, partial, or axiom. AI tools should not introduce unsafe code in proofs – doing so can bypass the logical guarantees. If an AI did produce an unsafe definition or used an axiom declaration to assume something unproved, treat that as a potential soundness bug. Remove or replace those with proper proofs. Lean will generally prevent using such unsafe features in theorem statements, but it’s best to double-check they aren’t present at all.

- Linters and style checks: The Lean community (especially mathlib) has linters that can catch certain classes of issues. For example, there are lint rules to detect definitions that should be marked protected, unused arguments, etc., and ones that ensure there are no instances of common mistakes. In Lean 4, some of these are still being developed, but one built-in linter warns if a section variable is unintentionally left unused in a theorem (to prevent forgetting hypotheses)[8]. While these linters focus on code quality and consistency rather than logical correctness, they can indirectly catch mistakes or inconsistencies in how the proofs are structured. Consider running #lint (if available in your project’s environment) to see if any warnings pop up.

By using these auditing methods, you add an extra layer of assurance on top of Lean’s core checking. They help catch subtle issues like an AI “proving” something by secretly assuming a stronger property or leaving a proof incomplete. However, note that these tools won’t catch a conceptual modeling error – for instance, if the statement proved isn’t the one you meant to prove. They only ensure that within the formal system, nothing fishy (like unproven axioms or unsound tactics) is going on. Always interpret the results: if #print axioms reports dependencies on things you didn’t expect, investigate why – it could be benign (e.g. using choice via a typeclass) or it could signal an unintended assumption.

## Independent Re-Checking with Alternate Kernels

For an additional layer of independent verification, you can use an alternative Lean kernel or external checker to re-verify your proofs. One such tool is Lean4Lean, an implementation of the Lean 4 kernel written in Lean itself (analogous to Coq’s idea of having a second checker)[9]. The Lean4Lean project provides a lean4lean binary that you can run on your compiled project. Essentially, it will take your .olean files (the compiled proofs) and re-check them through its own kernel implementation. This kind of double-check can guard against the (extremely unlikely) scenario of a bug in Lean’s C++ kernel, and it serves as a form of redundant proof verification.

Using Lean4Lean is a bit technical but doable: you compile the tool using lake (Lean’s package manager) and then run it pointed at your project. For example, if your project is in directory MyProj, you would navigate there and run something like:

lake env /path/to/lean4lean/.lake/build/bin/lean4lean

with appropriate arguments to check your modules[10]. By default, running it with no module argument will check all modules on the Lean search path, or you can specify a particular module to check. Lean4Lean will report if any proof or definition fails to type-check under its kernel. If it produces no errors, it means your proofs pass a second implementation’s scrutiny as well. (Keep in mind Lean4Lean is derived from the same codebase as Lean’s kernel, so it’s not 100% independent, but it’s maintained separately and could catch certain differences in behavior.) This tool does not upload anything – it operates on your local .olean files – so it’s privacy-safe.

Another approach to independent verification is cross-checking critical pieces in another proof assistant. This is a non-trivial endeavor, but for key lemmas you might try to replicate the proof in Coq, Isabelle/HOL, or Agda (translating your theory’s basics into that system). If successful, it provides high confidence that the theorem isn’t an artifact of one system’s quirk. However, this is often impractical for large theories and exposes your ideas to whoever is performing the re-formalization, so it may not meet the privacy requirement. If the theory is highly sensitive, lean4lean or similar “re-check within Lean” approaches are preferable.

Finally, note that Lean’s own export facilities (e.g., Lean can produce a list of declarations or even JSON of proofs) could be used to programmatically inspect the proofs for anomalies. Tools like LeanDojo or elan don’t exactly verify proofs but allow extraction of proof terms which you could analyze offline. These are advanced steps; for most users, simply rerunning the proofs in a fresh Lean environment or with Lean4Lean is sufficient to gain confidence. Remember, if Lean itself accepted the proofs, they are formal; an alternate checker is mostly for paranoia against compiler bugs or to satisfy an independent review criterion without sharing source code.

## Property-Based Testing and Semantic Validation

Even with all proofs checking out, you might worry about semantic flaws – cases where the AI proved something formally correct but not what you intended. One way to gain confidence in the “real-world” correctness of your Lean theories is to use property-based testing or example-based validation within Lean. The Lean community has a QuickCheck-like tool called SlimCheck (available in Lean’s mathlib4 library) that allows you to test propositions for counterexamples[11]. In property-based testing, you state a property (for instance, a theorem’s proposition or a conjecture) in a way that Lean can evaluate on concrete examples, and the framework will generate many random test cases to see if the property holds. If it finds a counterexample, that means either the theorem is actually false or the formal statement doesn’t capture the intuitive property you expected – a big red flag.

For example, suppose you have a conjecture in your KO7 calculus about the outcome of a certain reduction sequence. You could write a Lean function that performs a bounded number of steps of that reduction (if it’s executable), and then use SlimCheck to randomly generate small instances of inputs to test whether the property holds. If SlimCheck finds a violation (i.e. it produces a specific counterexample term where your proposition fails), then there is a serious issue: either the AI’s “proof” used an assumption that ruled out that case, or the theory has a bug. On the other hand, if no counterexample is found after extensive testing, you gain more confidence that the theorem is likely true in the sense you expect (this is not a proof, but it’s useful reassurance)[12].

Lean’s SlimCheck works by requiring a Checkable instance for your proposition – effectively a way to randomize inputs and evaluate the statement to a boolean. Many standard types (like numbers, lists, etc.) have such instances. You can also integrate testing into your build: for instance, using the LSpec testing framework, you can write Lean code that asserts certain test outcomes and have lake build fail if a test doesn’t pass. This way, your CI can run both the proof check and a battery of tests. Notably, you can even test partial functions or non-provable properties in Lean’s code by writing examples and expected results (unit tests)[13]. This won’t affect the logic of your proofs, but it can catch mismatches between your intuition and the formalization. For example, if an AI wrote a recursive function intended to compute an ordinal measure and you’re not entirely sure it’s correct, you could test it on small inputs against a reference implementation or known outcomes.

Limitations of testing: Keep in mind that if a theorem is formally proven in Lean, it means within Lean’s axioms it’s universally true. So finding a “counterexample” means either (a) you found an input that breaks an unstated assumption (thus the formal claim was too broad), or (b) there is an inconsistency in your axioms (which would be very serious). Usually, property testing is more helpful to catch cases where the model might be wrong – e.g., your formalization of the problem allows a weird edge case that your intuition missed. It can also catch if an AI introduced overly strong preconditions: for instance, maybe an AI proved a theorem assuming a certain condition implicitly. By testing scenarios that violate that condition, you might see the property fail, alerting you that the formal theorem wasn’t as unconditional as you thought.

In summary, property-based testing in Lean (via SlimCheck/LSpec) is a privacy-preserving way to validate semantics. All tests run locally, and you don’t have to reveal your theory to anyone. While it doesn’t provide a guarantee, it’s an excellent supplement to formal proofs for confidence. Use it to sanity-check critical properties, especially those that are easily interpretable computationally.

## Secure External Review Options (Limited Disclosure)

If you reach a point where you desire an external review for extra assurance, but cannot disclose the full theory, there are ways to do this in a controlled manner:

- Compiled library review: Lean’s compilation separates interface from implementation (similar to how .olean files contain compiled definitions/proofs). You could package your core theory as a compiled Lean library – basically share the .olean files (and any needed interface files with declarations and statements, but without proof scripts or sensitive implementation details). An external verifier (a colleague or hired expert under NDA) could then use these oleans to check that your theorems and proofs type-check against the provided interface. They wouldn’t see the actual content of your definitions (the intellectual property), just the signatures and the statements of theorems. Using Lean, they can verify that the proofs are complete (no sorry), and that no additional axioms beyond those in the interface are used. Essentially, you’d be giving them a black-box library: they can confirm it’s internally consistent and that your high-level theorems follow from your assumptions. What they can’t do is critique whether your axioms or definitions make sense – since those are hidden – but this method ensures you’re not accidentally relying on something outside the provided axioms.

- Partitioning the theory: Another tactic is to partition your work into “sensitive core” and “reviewable periphery.” The sensitive core (KO7 calculus rules, etc.) could be abstracted as assumptions or an opaque module. On top of that, you prove a number of results (lemmas, theorems). You can ask an external party to review those proofs given the core as a black box. They might, for instance, attempt to verify that no contradiction can be derived from your core plus the derived lemmas. This could be done by providing them with a special version of the theory where the core is replaced by axiom declarations representing each unpublished rule (or a sealed constant with properties). They would then check that all the proofs of the peripheral lemmas don’t require any additional hidden assumptions. This approach is tricky – it requires carefully deciding what you can expose – but it means the reviewer can validate the reasoning of the AI-generated proofs without seeing the secret sauce of your theory.

- NDA and private expert review: If you do need a human expert to go over everything (including the core theory) for maximum assurance, ensure it’s done under a strict confidentiality agreement. Preferably, choose someone who can do the review on an offline machine. They could, for example, come to your site or use a secured remote desktop into an isolated environment that has the code, so the code never leaves your control. While this is a “human” solution (which the question prefers to avoid unless necessary), it’s worth mentioning as a last resort for catching high-level conceptual flaws. A human reviewer can notice if the theorem you proved is not the theorem you think you proved – something no automated tool can truly grasp. If you go this route, structure the collaboration such that the reviewer doesn’t inadvertently learn more about the theory than needed (e.g., focus them on verifying the steps of proofs, not on coming up with new ideas).

Caveats: Even with partial disclosure (like compiled files or abstract interfaces), you are placing some trust in the external party. They might infer aspects of your theory or at least know the statements of your main results. If the theory is truly sensitive, you’d restrict this to a trusted few. Moreover, external reviewers – whether software or human – can only check for internal consistency and alignment with the formal statements. They cannot ensure that your formal statements capture exactly the real-world meaning (that’s a recurring theme!). So while these methods can greatly increase confidence and catch errors, always pair them with careful internal reasoning about your model.

In conclusion, a combination of software-based strategies will give you the rigorous verification you need: Lean’s own checker for core correctness, isolated CI for ongoing validation, auditing tools for any hidden issues, and property-based tests for semantic checks. These can all be done without exposing your work. Only if further assurance is needed do you consider involving external eyes, and even then, techniques like sharing only compiled proofs or partial information can protect your intellectual property. By systematically applying these methods, you should be able to catch any “fundamental reasoning flaws” from AI-generated proofs. Lean’s ecosystem is built to make proofs trustworthy by construction, so most flaws will either be caught by the toolchain or manifest as a clearly undesirable dependency. Remain mindful of the distinction between formal correctness and correctness with respect to your intent – use the tools for the former and your own careful review for the latter[5]. With this approach, you can confidently verify your Lean 4 formalization of the KO7 calculus in complete privacy and with high assurance.

Sources:

- Lean 4 documentation and community resources on proof checking, termination, and axiom auditing[1][3][4][7].

- Lean 4 CI and isolation advice from community Q&A[6].

- Lean4Lean project (Mario Carneiro) for independent kernel verification[10].

- SlimCheck property-based testing lecture notes[11].

- Discussion on Lean’s kernel trust and limits of automatic checking[5].

[1] Lean enables correct, maintainable, and formally verified code

https://lean-lang.org/

[2] User Guide — LeanDojo 2.2.0 documentation


[3] [8] Lean 4.11.0 — Lean

https://web.archive.org/web/20250414154623/https://lean-lang.org/blog/2024-9-1-lean-4110/

[4] lean4: usage for sorry vs admit - Proof Assistants Stack Exchange

https://proofassistants.stackexchange.com/questions/4541/lean4-usage-for-sorry-vs-admit

[5] New Foundations is consistent – a difficult mathematical proof proved using Lean | Hacker News

https://news.ycombinator.com/item?id=40130924

[6] Offline install of Lean - Proof Assistants Stack Exchange

https://proofassistants.stackexchange.com/questions/3997/offline-install-of-lean

[7] lean4 - In Lean 4, why and how do certain definitions need axioms, and others don't? - Proof Assistants Stack Exchange

https://proofassistants.stackexchange.com/questions/4759/in-lean-4-why-and-how-do-certain-definitions-need-axioms-and-others-dont

[9] [10] GitHub - digama0/lean4lean: Lean 4 kernel / 'external checker' written in Lean 4

https://github.com/digama0/lean4lean

[11] [12] Lecture 37: Demo of Slim Check


[13] Zulip Chat Archive



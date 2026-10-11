# Disclosure

JD Jones directed this project. Claude (Anthropic) in Claude Code was used throughout, and the repository was written in
that process: Graham's texts were read as printed pages (the 1966 paper from the Bell System Technical Journal scan; the
1969 paper from the author's scan on 2026-10-09, not re-read at the later audits because its host was unreachable, its
locators being that reading's and its two theorems checked against his 1972 survey, read from a PDF the owner
supplied), Dósa's 2004 note was read in the journal's volume and Della Croce and Scatamacchia's survey on arXiv, and
the statements, the standard-library replay, the Lean proofs, the prior-art searches and the documents were produced.
Chen's and Coffman–Sethi's papers were not read; their statements are taken from that survey. GPT (OpenAI) was used
once, for a pre-submission consult on the tree at bbb9373 (11 October 2026): its proposals were checked here, and what
was adopted passed the full verification gate before it entered the tree. The proofs are not the papers': the LPT bound is proved by a
counting argument in place of Graham's exchange argument, and Dósa's theorem by counting the jobs of each machine in
the two schedules in place of his minimal-counterexample argument (PROOF.md). The papers are cited, not copied.
`scripts/core_notation_audit.lean` is the Palomar registry's own renderability audit script
(PalomarRegistry/PalomarSubmission), copied with a three-line provenance comment; no other code is derived from another
project, and the neighbouring Lean and Isabelle work named in README.md is cited, not used. Verification status is stated
in VERIFICATION.md. No independent human review or source-author endorsement is claimed.

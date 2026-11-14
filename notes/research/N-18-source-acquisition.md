# N-18: Source acquisition and pattern data provenance

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-18` |
| Title | Retrieve and read the primary sources; establish where cell-exact pattern data comes from |
| Kind | source synthesis |
| Addresses | `Q-9`; supports `Q-4`–`Q-7`, `Q-10` and every pattern note |
| Depends on | none |
| Dependency requirement | none |
| Produces | upgraded access levels and locators in `notes/sources.md`; a data-provenance rule; pattern files (or references) for `N-05`–`N-11`; updates to `N-10`–`N-13`, `N-17` |
| Difficulty | routine, but partly blocked by access: the LifeWiki refuses automated retrieval and several sources are books |
| Status | stated |
| Implementation status | not started |
| Implementation evidence | none |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 2026-11-14: seeded |

## Purpose and scope

The seeding relied on summaries and snippets for most sources (`notes/sources.md`). Decisions
`Q-5`–`Q-7` and all component notes need the primary texts and exact pattern data.

## Dependencies

None.

## Sources and prior work

Access status on 2026-11-14:

- `conwaylife.com/wiki` (user-supplied): HTTP 403 for automated fetch. The mirror
  `conwaylife.njohnston.ca/wiki` worked for the four pages tried.
- `uwe-repository.worktribe.com` (Rendell's thesis): HTTP 403.
- `S-07` arXiv PDF: retrieved and read.
- `S-11` book PDF (≈ 91 MB): located, not downloaded.

## Theory development

Tasks, in order of value:

1. `S-11` (Johnston–Greene): download the PDF; read ch. 9 (Universal Computation) for the
   route decision `N-13`, ch. 6–8 for `N-10`, ch. 11–12 for `N-17`; record page-level locators.
2. `S-10` (Chapman): retrieve the archived page and the pattern; list the component types of
   the register machine.
3. `S-14` (Durand–Róka): obtain the text for `N-12`.
4. `S-08` parts 1–3 and the HOL4 development accompanying `S-07` (repository location not
   given on the arXiv page; find it): gate patterns and specifications.
5. Sliding block memory salvo geometries (`N-11`): from the Life Lexicon, the mirror wiki or
   Golly's pattern collection.
6. `S-09`: thesis or book, for the R2 comparison only.
7. `S-02`, `S-03`: books; need the user's help if they are to be read.

Data-provenance rule (proposal): every pattern used in Lean is stored as explicit cells in a
Lean `def`, with a comment naming the source file or page, its retrieval date and the RLE
string; an imported pattern has no authority — every property is proved from the cells. Check
the licence of any pattern collection before copying files into the repository; a pattern's
cell coordinates as such are facts, but record the question rather than assume.

## Claims and evidence

None.

## Difficulty, barriers and readiness

Ready now. The user may be able to supply sources that block automated access (LifeWiki pages,
books).

## Outputs and next dependencies

Raises the readiness of `N-10`, `N-11`, `N-12`, `N-13`, `N-17`.

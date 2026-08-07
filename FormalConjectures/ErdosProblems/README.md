# Erdős Problems

The official list of Erdős problems can be found at [erdosproblems.com](https://www.erdosproblems.com), managed by Thomas Bloom.

The purpose of this README is to standardize Lean formalization rules for Erdős problems. These standards will make it easier for new contributors to navigate the various formalizations within this repository.

## Naming Theorems
An Erdős problem usually consists of two parts:
1. **The main problem(s)**: The text within the red or green box on the website.
2. **The additional text**: The text provided below the red or green box.

### Main Problem(s)
Main problems may be presented as single questions, multi-part questions, requests for boundary estimates, or descriptions of functional behavior. Use the following naming standards for each case:

* **Single Questions**
    Use the format: `erdos_{N}`

* **Multi-part Questions**
    Use the convention: `erdos_{N}.parts.i`, `erdos_{N}.parts.ii`, etc.
    *(Note: In this case, there will not be a standalone `erdos_{N}` theorem.)*

* **Estimate Questions**
    The standard pattern is: `erdos_{N}.lower_bound` and `erdos_{N}.upper_bound`
    *Note: If a strict equality is proven, use `erdos_{N}`.*

* **Behavioral Descriptions**
    We do not currently have a standardized example for this case.

### Additional Text
For variants found in the additional text, the naming convention is:
`erdos_{N}.variants.{name}`

Choose a name that is descriptive of the variant. A common case is when the variant is a solved case for the main problem, but only for `k \geq 2`. In this case, the name could be `erdos_{N}.variants.k_geq_2`. Another common case is when a variant of the main problem is conjectured by another author. In this case, the name could be `erdos_{N}.variants.{author}`.

## Docstrings
Please keep docstrings as close as possible to the text on the Erdős Problems website. You should generally be able to copy and paste the LaTeX statements into the docstrings with only minor formatting adjustments.

The verbatim problem text should appear **only once** — in the theorem docstring, not repeated in the module header docstring (`/-! ... -/`). The module header should contain the problem title and references only.

## References
If the website lists references, include them at the top of the file and reference them via their citation. You can copy these directly from the "View the LaTeX source" section of the website.
An example of this would be:

**Example**:
```
*References:*
- [erdosproblems.com/{N}](https://www.erdosproblems.com/{N})
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
```

## Before requesting review

The general checklist lives in
[`AGENTS.md`](../../AGENTS.md#quality-checklist). Two corrections specific to
Erdős problems come up most often in review:

1. **Docstrings quote the website verbatim.** Copy the LaTeX from
   erdosproblems.com rather than rephrasing it. Only deviate to fix a genuine
   error or inaccuracy in the original formulation.
2. **Solved problems cite the solution.** The text below the problem box
   typically explains who solved it and in which paper; copy that sentence
   verbatim into the docstring as well.

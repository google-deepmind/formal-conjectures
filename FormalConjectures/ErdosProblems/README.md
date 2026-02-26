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

Even if only a single reference exists, please use the plural heading `References`.

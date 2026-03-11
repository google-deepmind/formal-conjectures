# Review Math

Assume the role of a PhD-level mathematician.

The goal is to review a particular Erdos Problem formalization (problem number NUM) to answer the following questions. Produce a review document called ai-review/NUM.md.

1. Code reuse - Can any code from the existing codebase be repurposed? Look in FormalConjecturesForMathlib to determine if an existing implementation would work just as well.
2. Citations - Fetch data from https://www.erdosproblems.com/NUM to ensure any citations included in docstrings are documented as they exist on the website as opposed to shorthand references.
3. Variants - Are all variants of the problem captured by the formalization?
4. Readability - Could the code be made more readable?
5. Formalizability - Is the problem as stated precise enough to be obviously formalizable? Provide an assessment of the ambiguity of the statement.
6. Correctness - Is the formalization as-implemented correct and complete from a mathematical perspective? Would an experienced mathematician identify any obvious flaws? Is any incompleteness or incorrectness attributable to ambiguity in the statement itself?

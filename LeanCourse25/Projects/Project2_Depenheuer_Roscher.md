Authors: Joachim Roscher and Nora Depenheuer
Project: Möbius strip & Klein bottle

- Firstly, we implemented the Möbius strip and the Klein bottle as quotients of the unit square [0,1] × [0,1] ⊆ ℝ².
- Then we embedded them into ℝ³ resp. ℝ⁴ by formulas we found on Wikipedia resp. math.stackoverflow.com and mathoverflow.net. Sadly, the proof of injectivity and homeomorphism is partly sorry'ed.
- We proved that the Möbius Strip is homotopy equivalent to the circle.
For simplicity, we defined the circle as a quotient of [0,1] by glueing together both endpoints. For future use it may be useful to change the proof to the mathlib notion of the circle in ℂ.
In the proof we have two sorry's since we couldn't find out how to list all preimages of some point via Quotient.mk, i.e. all elements of the equivalence class of said point.

We haven't done anything with AI.

import FormalConjectures.Util.ProblemImports

open Erdos36

-- Key helper: For finite computations, we need to relate noncomputable defs to
-- computable alternatives.

-- The proof structure for M n = v:
-- 1. Show v is in the set (upper bound): exhibit partition with MaxOverlap = v
-- 2. Show v is a lower bound: every partition has MaxOverlap ≥ v

-- Helper: Overlap is bounded by A.card (trivially)
-- Helper: MaxOverlap for finite sets is bounded

-- For small n, the key approach:
-- Upper bound: exhibit a concrete partition and compute MaxOverlap using norm_num/decide
-- Lower bound: pigeonhole — the (A ×ˢ B) has n² pairs, differences range in -(2n-1)...(2n-1)
--   so by pigeonhole, some difference has multiplicity ≥ n²/(4n-1)

-- For n=1: n²/(4n-1) = 1/3, so MaxOverlap ≥ 1
-- For n=2: n²/(4n-1) = 4/7, so MaxOverlap ≥ 1
-- For n=3: n²/(4n-1) = 9/11, so MaxOverlap ≥ 1 (but actual is 2)
-- For n=4: n²/(4n-1) = 16/15 > 1, so MaxOverlap ≥ 2
-- For n=5: n²/(4n-1) = 25/19 > 1, so MaxOverlap ≥ 2 (but actual is 3)

-- Actually, the pigeonhole bound is too weak for n=3 and n=5.
-- We need a stronger argument for those.

-- Alternative approach for small n: just enumerate all partitions.
-- For n=1, there are C(2,1) = 2 partitions (but they're symmetric).
-- For n=2, there are C(4,2) = 6 partitions.
-- For n=3, there are C(6,3) = 20 partitions.
-- For n=4, there are C(8,4) = 70 partitions.
-- For n=5, there are C(10,5) = 252 partitions.

-- This is feasible computationally! We can use native_decide or decide for the
-- lower bound by enumerating all partitions.

-- But the definitions are noncomputable, so we need to bridge them.

-- Let me try a different approach: create computable versions and bridge lemmas.

-- Computable MaxOverlap: take max over k in the range -(2n)...(2n)
def MaxOverlap' (A B : Finset ℤ) (bound : ℤ) : ℕ :=
  (Finset.Icc (-bound) bound).sup' ⟨0, Finset.mem_Icc.mpr ⟨neg_nonpos_of_nonneg (by omega), by omega⟩⟩
    (Overlap A B)

-- The MaxOverlap equals MaxOverlap' when bound is large enough
-- because Overlap A B k = 0 for |k| > max(A) - min(B)

-- Actually, let me think about this differently.
-- The Overlap A B k counts pairs (a,b) with a-b=k. If A ⊆ {1,...,2n} and B ⊆ {1,...,2n},
-- then a-b ranges from 1-2n to 2n-1, i.e., -(2n-1) to 2n-1.
-- So Overlap A B k = 0 for |k| ≥ 2n.
-- Therefore MaxOverlap A B = sup over k ∈ {-(2n-1),...,2n-1} of Overlap A B k.

-- But iSup is over ALL integers. We need to show that the sup over ℤ equals
-- the sup over the finite range.

-- This is getting complex. Let me try the most direct approach that actually compiles.
-- For M_one, there are only 2 partitions to check. Let me try native_decide on
-- a computable reformulation.

-- Actually, let me try the approach from the golfed proof but cleaned up.
-- The golfed proof of M_four uses:
-- 1. csInf_eq via IsLeast
-- 2. For the lower bound member: exhibit partition {1,2,4,8} and compute
-- 3. For the lower bound property: every partition has MaxOverlap ≥ 2

-- Let me try M_one first with this pattern.

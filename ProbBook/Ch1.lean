import Mathlib.Init.Set
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Tactic.DeriveFintype

variable {Ω : Type u}

-- Definition 1.2
class DistFunc (Ω : Type u) where
  m : Ω → ℝ
  hp (ω : Ω) : m ω ≥ 0
  hs : (∑' ω, (m ω)) = 1

noncomputable
def P [d : DistFunc Ω] (E : Set Ω) := (∑' (ω : E), (d.m ω))

-- Example 1.7
namespace Example_1_7

inductive Coin2 where
  | HH
  | HT
  | TH
  | TT
  deriving Fintype

open Coin2

noncomputable
instance dist : DistFunc Coin2 := {
  m := fun (x : Coin2) => 1/4
  hp := by simp
  hs := by
    rw [one_div, tsum_const]
    have hc : Nat.card Coin2 = 4 := by aesop
    rw [hc]
    norm_num
}

lemma dist_pairwise : Pairwise (fun (x y : Coin2) => dist.m x = dist.m y) := by
  exact fun ⦃i j⦄ ↦ congrFun rfl

def E : Finset Coin2 := ⟨{HH,HT,TH},by simp⟩

example : @P _ dist E = 3/4 := by
  rw [P, dist]
  aesop

def F : Finset Coin2 := ⟨{HH,HT},by simp⟩

example : @P _ dist F = 2/4 := by
  rw [P, dist]
  aesop

end Example_1_7

--Theorem 1.1
--1
theorem P_positivity [d : DistFunc Ω] (E : Set Ω) (hsumE : Summable fun i : E ↦ d.m ↑i):
  P E ≥ 0 := by
  unfold P
  have hp (ω : E) : d.m ω ≥ 0 := by
    exact d.hp ↑ω
  calc
    ∑' (ω : ↑E), d.m ↑ω ≥ ∑' (i : ↑E), 0 := by rel [(tsum_le_tsum hp (summable_zero) (hsumE))]
    _ ≥ 0 := by simp

--2
theorem P_eq_one [d : DistFunc Ω]:
  P (Set.univ : Set Ω) = 1 := by
  unfold P
  rw [tsum_univ]
  exact d.hs

--3
theorem P_le_of_subset [d : DistFunc Ω] (E : Set Ω) (F : Set Ω) (hss : E ⊂ F)
  (hsumE : Summable fun i : E ↦ d.m ↑i)
  (hsumF : Summable fun i : F ↦ d.m ↑i):
  P E ≤ P F := by
  unfold P
  have hs : E ⊆ F := subset_of_ssubset hss
  let e : E → F := fun x => ⟨x,by aesop⟩
  have hi : Function.Injective e := by
    unfold Function.Injective
    aesop
  have h1 : ∀ c ∉ Set.range e, 0 ≤ d.m c := fun c _ ↦ d.hp ↑c
  have h2 : ∀ (i : E), d.m i ≤ d.m (e i) := fun i ↦ Preorder.le_refl (d.m ↑i)
  exact tsum_le_tsum_of_inj e hi h1 h2 hsumE hsumF

--4
theorem P_union_disjoint [d : DistFunc Ω] (A : Set Ω) (B : Set Ω)
  (hd : Disjoint A B)
  (hsumA : Summable fun i : A ↦ d.m ↑i)
  (hsumB : Summable fun i : B ↦ d.m ↑i):
   P (A ∪ B) = P A + P B := by
  unfold P
  exact tsum_union_disjoint hd hsumA hsumB

--5
theorem P_compl [d : DistFunc Ω] (A : Set Ω)
  (hsum : Summable fun i : A ↦ d.m ↑i)
  (hsumc : Summable fun i : (Set.compl A) ↦ d.m ↑i):
   P (Aᶜ) = 1 - P (A) := by
  rewrite [← (@P_eq_one Ω d)]
  rewrite [(Set.compl_union_self A).symm]
  rewrite [P_union_disjoint]
  simp
  exact Set.disjoint_compl_left_iff_subset.mpr fun ⦃a⦄ a ↦ a
  exact hsumc
  exact hsum

lemma P_empty [DistFunc Ω] : P (∅ : Set Ω) = 0 := by
  rw [P]
  exact tsum_empty

open Finset
--Theorem 1.2
theorem P_fin_pairwise_disjoint_union [d : DistFunc Ω]
  (n : ℕ)
  (A : ℕ → Set Ω)
  (hpd : (range n : Set ℕ).Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ range n , A i) = ∑ i ∈ (range n), P (A i) := by
  unfold P
  rw [tsum_finset_bUnion_disjoint hpd (by exact fun i _ ↦ hsum i)]

--Some modified versions
theorem P_fin_pairwise_disjoint_union2 [d : DistFunc Ω]
  (n : ℕ)
  (I : Finset (Fin n))
  (A : (Fin n) → Set Ω)
  (hpd : Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ I, A i) = ∑' (i : I), P (A i) := by
  unfold P
  have hpd2 : (I : Set (Fin n)).Pairwise (Disjoint on A) := by
    rw [Pairwise] at hpd
    intro x _ y _
    exact fun a ↦ hpd a
  rw [tsum_finset_bUnion_disjoint hpd2 (by exact fun i _ ↦ hsum i)]
  rw [←(Finset.tsum_subtype I (fun i => (∑' (x : ↑(A i)), d.m ↑x)))]

theorem P_fin_pairwise_disjoint_union3 [d : DistFunc Ω]
  (n : ℕ)
  (I : Finset (Fin n))
  (A : (Fin n) → Set Ω)
  (hpd : (I : Set (Fin n)).Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i ∈ I, A i) = ∑' (i : I), P (A i) := by
  unfold P
  rw [tsum_finset_bUnion_disjoint hpd (by exact fun i _ ↦ hsum i)]
  rw [←(Finset.tsum_subtype I (fun i => (∑' (x : ↑(A i)), d.m ↑x)))]

theorem P_fin_pairwise_disjoint_union4 [d : DistFunc Ω]
  (n : ℕ)
  (A : (Fin n) → Set Ω)
  (hpd : Pairwise (Disjoint on A))
  (hsum : ∀j , Summable fun i : A j ↦ d.m ↑i):
    P (⋃ i , A i) = ∑' i , P (A i) := by
  have hpd2 : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).Pairwise (Disjoint on A) := by
    rw [Pairwise] at hpd
    intro x _ y _
    exact fun a ↦ hpd a
  have hu : (⋃ i , A i) = ⋃ i ∈ Finset.univ, A i := by simp
  unfold P
  rw [hu]
  rw [tsum_finset_bUnion_disjoint hpd2 (by exact fun i _ ↦ hsum i)]
  exact Eq.symm (tsum_fintype fun b ↦ ∑' (ω : ↑(A b)), d.m ↑ω)

--Theorem 1.3
theorem P_fin_pairwise_disjoint_inter [d : DistFunc Ω]
  (n : ℕ) (A : ℕ → Set Ω)
  (hpd : (Finset.range n : Set ℕ).Pairwise (Disjoint on A))
  (huniv : Set.univ = (⋃ i ∈ range n, A i)) (E : Set Ω)
  (hsumEA : ∀j , Summable fun i : ↑(E ∩ A j) ↦ d.m ↑i):
    P E = ∑ i ∈ range n, P (E ∩ A i) := by
  let B : ℕ → Set Ω := fun i => E ∩ A i
  have hpdB : (Finset.range n : Set ℕ).Pairwise (Disjoint on B) := by
    unfold_let
    intro x xin y yin xy
    rw [Function.onFun_apply]
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← Set.inter_inter_distrib_left]
    replace hpd : (Disjoint on A) x y := by exact hpd xin yin xy
    rw [Function.onFun_apply] at hpd
    rw [Set.disjoint_iff_inter_eq_empty] at hpd
    simp_all only [Set.disjoint_iUnion_left, ne_eq, Set.inter_empty]
  have hsumB : ∀j , Summable fun i : B j ↦ d.m ↑i := by exact fun j ↦ hsumEA j
  have hu : ⋃ i ∈ range n, B i = E := by
    unfold_let
    simp only
    calc
    ⋃ i ∈ range n, E ∩ A i = E ∩ (⋃ i ∈ range n, A i) := by exact Eq.symm (Set.inter_iUnion₂ E fun i _ ↦ A i)
    _ = E ∩ Set.univ := by exact congrArg (Inter.inter E) (id (Eq.symm huniv))
    _ = E := by simp
  rw [← P_fin_pairwise_disjoint_union n B hpdB hsumB]
  rw [hu]

--Corollary 1.1
theorem P_inter_add_compl [d : DistFunc Ω]
  (A : Set Ω) (B : Set Ω)
  (hsum : Summable fun i : (Set.inter A B) ↦ d.m ↑i)
  (hsumc : Summable fun i : (Set.inter A Bᶜ) ↦ d.m ↑i):
    P A = P (A ∩ B) + P (A ∩ Bᶜ) := by
  let B' (i : ℕ) : Set Ω :=
    match i with
    | 0 => B
    | 1 => Bᶜ
    | _ => ∅
  have hpd : (Finset.range 2 : Set ℕ).Pairwise (Disjoint on B') := by
    intro x y hxy
    rw [Function.onFun_apply]
    have h1 : Disjoint B Bᶜ := Set.disjoint_compl_right_iff_subset.mpr fun ⦃a⦄ a ↦ a
    have h2 : Disjoint Bᶜ B := id (Disjoint.symm h1)
    aesop
  have huniv : Set.univ = ⋃ i ∈ range 2, B' i := by
    rw [range_succ]
    simp_all only [coe_range, range_one, mem_insert, mem_singleton, Set.iUnion_iUnion_eq_or_left,Set.iUnion_iUnion_eq_left, Set.compl_union_self, B']
  have hsumB' : ∀j, Summable fun (i : @Inter.inter (Set Ω) _ A (B' j)) ↦ d.m ↑i := by
    intro j
    match j with
      | 0 => exact hsum
      | 1 => exact hsumc
      | x+2 =>
        have hx2 : B' (x+2) = ∅ := rfl
        rw [hx2]
        rw [Set.inter_empty A]
        simp [summable_empty]
  rw [P_fin_pairwise_disjoint_inter 2 B' hpd huniv A hsumB']
  rw [sum_range_succ]
  rw [sum_range_succ]
  simp

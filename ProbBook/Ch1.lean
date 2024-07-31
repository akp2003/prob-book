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

--Theorem 1.2
theorem P_fin_pairwise_disjoint_union [d : DistFunc Ω]
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

--Theorem 1.3
theorem P_fin_pairwise_disjoint_inter [d : DistFunc Ω]
  (n : ℕ) (A : (Fin n) → Set Ω)
  (hpd : Pairwise (Disjoint on A))
  (huniv : Set.univ = (⋃ i, A i)) (E : Set Ω)
  (hsumEA : ∀j , Summable fun i : ↑(E ∩ A j) ↦ d.m ↑i):
    P E = ∑' i, P (E ∩ A i) := by
  let B : (Fin n) → Set Ω := fun i => E ∩ A i
  have hpdB : Pairwise (Disjoint on B) := by
    unfold_let
    intro j k hjk
    rw [Function.onFun_apply]
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← Set.inter_inter_distrib_left]
    replace hpd : (Disjoint on A) j k := by exact hpd hjk
    rw [Function.onFun_apply] at hpd
    rw [Set.disjoint_iff_inter_eq_empty] at hpd
    simp_all only [Set.disjoint_iUnion_left, ne_eq, Set.inter_empty]
  have hsumB : ∀j , Summable fun i : B j ↦ d.m ↑i := by exact fun j ↦ hsumEA j
  have hu : ⋃ i, B i = E := by
    unfold_let
    rw [← Set.inter_iUnion]
    simp [← huniv]
  rw [← P_fin_pairwise_disjoint_union n B hpdB hsumB]
  rw [hu]

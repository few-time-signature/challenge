import Candidate.Constructions.PORS.ChainColumn
import Candidate.Constructions.PORS.ChainDominance
import Candidate.Constructions.PORS.SingleCover

namespace PoissonDAG.PORS.ChainExperiment
open ChainLaw ChainRefined Literal FiniteKernels

abbrev Extras := Buckets × DepthRanks
abbrev All := (Fin p.K → Fin ChainRankGate.C) × Extras

private def columns (q : Nat) :
    (Fin q → Extras) × All ≃ (Fin p.K → ChainColumn.Draw (Fin ChainRankGate.C) q) where
  toFun x i := ((x.2.2.1 i,fun j => (x.1 j).1 i),fun j => (x.1 j).2 i,x.2.1 i,x.2.2.2 i)
  invFun y := (fun j => (fun i => (y i).1.2 j,fun i => (y i).2.1 j),
    (fun i => (y i).2.2.1),fun i => (y i).1.1,fun i => (y i).2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def product (q : Nat) (hs : Fin q → H) (hb : Fin q → Extras) (t : All) : ℚ :=
  ∏ i, ChainColumn.hit baseSlot (fun j => slot (hs j) i) (columns q (hb,t) i)

private theorem independent {A : Type} [Fintype A] (n : Nat) (f : Fin n → A → ℚ) :
    average (fun x : Fin n → A => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  unfold average; rw [←Fintype.prod_sum,Finset.prod_div_distrib,Fintype.card_fun]; simp

private theorem averaged (q : Nat) (hs : Fin q → H) :
    average (fun hb : Fin q → Extras => average (product q hs hb)) ≤ p.simplexBucket coefs q ^ p.K := by
  rw [←average_prod (fun x : (Fin q → Extras) × All => product q hs x.1 x.2)]
  let f (i : Fin p.K) := ChainColumn.hit baseSlot (fun j => slot (hs j) i)
  apply (average_equiv (columns q) _ (fun x => ∏ i,f i (x i)) (fun _ => rfl)).le.trans
  rw [independent]
  calc
    _ ≤ ∏ _ : Fin p.K,p.simplexBucket coefs q := by
      apply Finset.prod_le_prod
      · intro i _
        unfold average
        apply div_nonneg _ (Nat.cast_nonneg _)
        exact Finset.sum_nonneg (fun x _ => by change 0≤ChainColumn.hit _ _ x; unfold ChainColumn.hit; split <;> norm_num)
      · intro i _
        exact ChainColumn.averaged baseSlot (fun j => slot (hs j) i)
          ((Fintype.card_fin _).trans ChainRankGate.c_eq) base_requests_injective
    _ = _ := by simp

noncomputable def expand : Fin (scheme p).accepted.length ↪ All where
  toFun t := (supportRank (accepted t).1,(accepted t).2)
  inj' x y eq := by
    apply accepted.injective; apply Prod.ext
    · apply slots_injective; funext i
      exact congrArg baseSlot (congrFun (congrArg Prod.fst eq) i)
    · exact congrArg (fun z : All => z.2) eq

private theorem product_nonneg (q hs hb t) : 0≤product q hs hb t := by
  unfold product; apply Finset.prod_nonneg
  intro i _; unfold ChainColumn.hit; split <;> norm_num

private theorem dominates (q : Nat) (h : Fin q → Fin (scheme p).accepted.length)
    (t : Fin (scheme p).accepted.length) :
    (if (scheme p).covered (indexHistory (scheme p).accepted h) (scheme p).accepted[t]
      then (1:ℚ) else 0) ≤ product q (fun j => (accepted (h j)).1) (fun j => (accepted (h j)).2) (expand t) := by
  split
  next hc =>
    have all (i : Fin p.K) : ChainColumn.possible baseSlot (fun j => slot (accepted (h j)).1 i)
        (columns q ((fun j => (accepted (h j)).2), expand t) i) := by
      intro j
      obtain ⟨z,l,hb,hl,hd⟩ := ChainHistorical.covered_slot h t hc i j
      exact ⟨z,l,hb,hl,hd⟩
    simp only [product,ChainColumn.hit,if_pos (all _),Finset.prod_const_one,le_refl]
  next => exact product_nonneg .. 

private theorem all_card : Fintype.card All = p.domain := by
  simp only [All,Extras,DepthRanks,Buckets,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    ChainDepths.chain_depth_ranks.2,ChainRankGate.c_eq,Row.domain,mul_pow]
  ac_rfl

private theorem extend_sum {A X : Type} [Fintype A] [Fintype X] (e : A ↪ X) (f : A → ℚ)
    (g : X → ℚ) (good : ∀ x,0≤g x) (major : ∀ a,f a ≤ g (e a)) : (∑ a,f a) ≤ ∑ x,g x := by
  classical
  apply (Finset.sum_le_sum (s:=Finset.univ) (fun a _ => major a)).trans
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => good x)

private theorem mass (s : Scheme) (q : Nat) (pos : 0<s.accepted.length) :
    s.coverCoefficient q = average (fun h : Fin q → Fin s.accepted.length =>
      ∑ t : Fin s.accepted.length,if s.covered (indexHistory s.accepted h) s.accepted[t] then (1:ℚ) else 0) /
      2^s.encoder.inputs := by
  rw [s.coverCoefficient_eq_acceptedProbability pos]
  unfold Scheme.tau Scheme.acceptedCoverProbability average
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,pow_succ]
  have nz : (s.accepted.length : ℚ)≠0 := by exact_mod_cast pos.ne'
  field_simp [nz] <;> ring

attribute [local irreducible] Literal.scheme Scheme.accepted Scheme.coverCoefficient Literal.shape

theorem history (q : Nat) : (scheme p).coverCoefficient q ≤ p.simplexEnvelope coefs q := by
  classical
  letI : Fintype H := Fintype.ofFinite _
  have pos : 0<(scheme p).accepted.length := by rw [ChainRankGate.accepted_count]; decide +kernel
  letI : Nonempty H := ⟨(accepted ⟨0,pos⟩).1⟩
  apply le_min
  · have cap := SingleCover.coefficient_of_count (scheme p) q ((scheme p).accepted.length:ℚ) pos
      (fun h => by
        have hh := Finset.card_le_univ (SingleCover.hits (scheme p) (indexHistory (scheme p).accepted h))
        exact_mod_cast (by simpa only [Fintype.card_fin] using hh :
          (SingleCover.hits (scheme p) (indexHistory (scheme p).accepted h)).card ≤ (scheme p).accepted.length))
    rw [ChainRankGate.accepted_count,literal_inputs] at cap; exact cap
  · let n : ℚ := Fintype.card All
    have nz : n≠0 := by change (Fintype.card All : ℚ)≠0; rw [all_card]; norm_num [ChainRefined.p,Row.domain,Row.buckets,Row.supports] <;> decide
    let e := (Equiv.piCongrRight (fun _ : Fin q => accepted)).trans (Equiv.arrowProdEquivProdArrow _ _ _)
    let T (h : Fin q → H) (b) := average (product q h b)
    have comp (h : Fin q → Fin (scheme p).accepted.length) :
        (∑ x : Fin (scheme p).accepted.length,if (scheme p).covered
          (indexHistory (scheme p).accepted h) (scheme p).accepted[x] then (1:ℚ) else 0)
        ≤ n*T (e h).1 (e h).2 := by
      have z := extend_sum expand _ _ (product_nonneg q _ _) (dominates q h)
      apply z.trans_eq
      change _ = n*(_/n)
      field_simp <;> rfl
    have a : average (fun h => n*T (e h).1 (e h).2) = n*average (fun h => average (T h)) := by
      rw [average_equiv e _ (fun x => n*T x.1 x.2) (fun _ => rfl),
        ←average_prod (fun x : (Fin q → H) × (Fin q → Extras) => T x.1 x.2)]
      unfold average; rw [←Finset.mul_sum]; ring
    have ht : average (fun h : Fin q → H => average (T h)) ≤ p.simplexBucket coefs q ^ p.K := by
      rw [←average_const (A:=Fin q → H) (p.simplexBucket coefs q ^p.K)]
      exact average_mono (averaged q)
    rw [mass _ q pos,literal_inputs]
    calc
      _ ≤ _ := div_le_div_of_nonneg_right (average_mono comp) (by positivity)
      _ = _ := congrArg (fun z : ℚ => z/2^p.r) a
      _ ≤ (n*(p.simplexBucket coefs q ^p.K))/2^p.r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by dsimp only [n]; rw [all_card]; ring

theorem certificate : V2.ConstructionCertificate chainBuckets 1188 := by
  apply chain_conditional
  exact { count := ChainRankGate.accepted_count
          work := fun _ h => (ChainRoutes.resources h).2
          labels := fun _ h => (ChainRoutes.resources h).1
          traversal := fun raw h => ⟨ChainRoutes.owner raw,ChainRoutes.depth raw,ChainRoutes.traversal h⟩
          historicalCount := history }

#print axioms certificate

end PoissonDAG.PORS.ChainExperiment

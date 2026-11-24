import YM.FormalBulk08.Bank.Cinder

/-! Add coarse letters to incoming kinetic+interaction. One line for any Lo-light operands. Budget Kith retained in SAME chosen width. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Bank
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {I J : Type*} [DecidableEq I] [Fintype I] [Fintype J]
def winging (I J : Type*) [DecidableEq I] : Row I (I⊕J) := fun i v=> v.elim (fun x=> unitRow I i x) (fun _=>0)
omit [Fintype I] [Fintype J] in
lemma wing_strip (σ : ℝ): (winging I J).strip σ 1 := fun x y=> by
   cases y with
   | inl v=> exact Work.F08.strip_unit x v
   | inr v=>exact stillborn zero_le_one (V:=I) (X:=J) x v
lemma barrel (n : Side) (p : Pap (Tor n I)) :
    PowerSeries.map (MvPolynomial.rename (fun v: Tor n I=>(v.1,Sum.inl (β:=J) v.2))).toRingHom p=PowerSeries.map (mixRows ((winging I J).acts n)).toRingHom p := by
   rw [show MvPolynomial.rename _=mixRows _ from ?_]; ext i; simp_rw [MvPolynomial.rename_X,mixRows,MvPolynomial.aeval_X]; rw [Finset.sum_eq_single ((i:Tor n I).1,Sum.inl i.2)]; swap
   · intro v _ hv; rcases v with ⟨x,j|j⟩
     · have hh : i ≠ (x,j) := fun he=> hv (by rw [he]);rw [show (winging I J).acts n i (x,Sum.inl j) = (unitRow I).acts n i (x,j) from rfl,acts_unit,Matrix.one_apply_ne hh,map_zero,zero_mul]
     simp [winging,Row.acts]
   swap; · simp
   rw [show (winging I J).acts n i (i.1,Sum.inl i.2)= (unitRow I).acts n i i from rfl, acts_unit,Matrix.one_apply_eq,map_one,one_mul]
variable {G : Gauge} {n f : Side} {P : Patch} {L : Lodge P} {η C : ℝ}

def altitude (P : Patch) (T : Pot G) (e r : ℕ):= jetty (scroll P.L (Loc G 1)).symm (T e r)
def atlas (P : Patch) (T : Pot G) (e r : ℕ) := pearl (lands (winging (Rim G P) (Loc G 1))) (altitude P T e r)
lemma yarn (S : StepData n f) (p : Pap (wire G f)) : joust (staging G S) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom p)=PowerSeries.map (mixRows ((winging (Rim G S.patch) (Loc G 1)).acts n)).toRingHom (joust (unitSplit G S 1) p) := by
   rw [←barrel n]; ext1 e; unfold joust; simp_rw [coeff_map]; simp only [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.rename_rename]; rfl
lemma tor_yarns (S : StepData n f) (T : Pot G) (hp : Vivid T) (e r) (i : Fin r) :
   rancho (joust (staging G S) (PowerSeries.map (MvPolynomial.rename Sum.inl).toRingHom (stone T f))) e r= pearl ((winging (Rim G S.patch) (Loc G 1)).acts n) (cum i n (altitude S.patch T e r)) := by
   rw [yarn]; have hh : cum i n (altitude S.patch T e r)=jetty (unitSplit G S 1).symm (cum i f (T e r)):=cum_jet S.ratio _ (hp.civil e r) i
   rw [hh,←hp.flower _ _ i f,←joust_level]
   unfold rancho; rw [coeff_map]; exact Lava.target ..

omit [DecidableEq I] in
lemma water_pearl {r : ℕ} {R : Tile (Biglot I) r} {S : (n:Side)→Tile (Tor n I) r} {M : Row I J} (h : M.strip η C) (H : Kith η R S) (i : Fin r) (hs : 0 < η) (hc : 0≤C) :
    Kith η (pearl (lands M) R) (fun n=>pearl (M.acts n) (S n)) := by
   obtain ⟨e,A,H⟩:= H
   have hh n := trundle n M h hc hs.le; exact ⟨sparkle_pearl e (landing_row _ (Row.rights _ _ h hs.le)) _ _ A hs H (.of_forall hh) i,1*(A*((Fintype.card I)*C)*((Fintype.card J)*C)^(r-1)),H.mono fun n hn=> hn.pearl (pier n I J η hs.le) (hh n)⟩
omit [DecidableEq I] in
lemma water_bills {r : ℕ} {R : Tile (Biglot I) r} {M : Row I J} {B : ℝ} (h : M.strip η C) (H : Bail (fame _) η R B) (hs : 0≤η) (hc : 0≤C):
    Bail (fame _) η (pearl (lands M) R) (1*(B*((Fintype.card I)*C)*((Fintype.card J)*C)^(r-1))) := H.pearl (bridge I J η hs) (grad_line M h hc)
lemma stable {I : Type*} [Fintype I] {η : ℝ} {r : ℕ} {R : Tile (Biglot I) r} (hs : 0 ≤ η) (h : Up R) (H : Bail (fame _) η R C) (i : Fin r) : Kith η R (fun n=>cum i n R):= ⟨spark R i hs H h,C,.of_forall fun n=>cum_charge i n h hs H⟩
end YM.FormalBulk08.Bank

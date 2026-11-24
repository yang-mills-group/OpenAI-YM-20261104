import YM.UVExt.MainTransfer
import YM.Next.FREE_KERNELS.Traffic
import YM.Next.FREE_KERNELS.Current

/-! Period row estimates for actual installed stencils in sup norm. Isotropic block factors (one side count); set H shape at the same two levels, not a newly chosen minimizer at each direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Laurent Bid Exterior Bloch Matrix Filter Tree Set Real
open Next.Free Work.F08
open scoped Topology ContDiff BigOperators Classical

section paper
variable {α β γ E : Type*} [Fintype α] [Fintype β] [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev WideBudget {γ δ : Type*} [Fintype δ] (K : Matrix γ δ ℝ) (C : ℝ) := ∀ i, ∑ j, ‖K i j‖ ≤ C
def actionFrame (K : Matrix α β ℝ) (v : β→E) := fun i=> ∑ j:β,K i j • v j
lemma wide_mul {K : Matrix γ α ℝ} {L : Matrix α β ℝ} {C D : ℝ} (h : WideBudget K C) (ht : WideBudget L D) (hd : 0≤D) : WideBudget (K*L) (C*D) := by
  intro i
  simp only [Matrix.mul_apply,←Finset.sum_mul]
  calc
     _ ≤ ∑ j:β,∑ k,‖K i k‖*‖L k j‖ := Finset.sum_le_sum fun j _ => (norm_sum_le ..).trans (le_of_eq <| Finset.sum_congr rfl fun k _=>norm_mul ..)
     _ ≤ ∑ k, ‖K i k‖ * D := (Finset.sum_comm.trans (Finset.sum_congr rfl fun k _=>Eq.symm <| Finset.mul_sum ..)).trans_le (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (ht k) (norm_nonneg _))
     _ ≤ _ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h i) hd
lemma row_zero {K : Row γ β} {σ : ℝ} {D} (h : K.strip σ D) (hs : 0≤σ) (n : Side) : WideBudget (K.acts n) (Fintype.card β * D) := fun i=>by simpa only [zero_mul, Real.exp_zero,one_mul] using (row_sprawl le_rfl (show K.strip 0 D from strip_mono h hs le_rfl) _ i)
lemma cross_zero {c f} (g : Ratio c f) {K : Cross g.count γ β} {σ D : ℝ} (h : K.strip σ D) (hs : 0≤σ) : WideBudget (installed g K) (Fintype.card β*D) := fun i=>show _ from row_zero h hs _ _
lemma frame_pay (v : β→E) {C : ℝ} {K : Matrix α β ℝ} (h : WideBudget K C) (hC : 0≤C) : ‖actionFrame K v‖ ≤ C*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => (norm_sum_le ..).trans <| calc
    _ ≤ ∑ j,‖K i j‖ * ‖v‖ := Finset.sum_le_sum fun j _=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ ≤ _ := by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
end paper

section gifts
private lemma buyKnots (k : ℝ) (j t : ℕ) : ∃ σ C, 0<σ ∧ 0<C ∧ ∀ P:Flight j t,∀ l:List Axis, 4≤j → 4≤t → 0<k → l.length≤j-2 →
      (Flight.groundPsi k P l).strip σ (C/(P.L.val:ℝ)^(2+l.length)) := by
   by_cases h : 4≤j ∧ 4≤t ∧ 0<k
   · rcases h with ⟨hj,ht,hk⟩
     obtain ⟨a,b,h₁,h₂,H⟩ := Flight.stockroom k hk hj ht
     exact ⟨a,b,h₁,h₂,fun P l _ _ _=>H P l⟩
   exact ⟨1,1,zero_lt_one,zero_lt_one,fun _ _ ht hk hl _=>False.elim (h ⟨ht,hk,hl⟩)⟩

private def knotWidth (k : ℝ) (j t : ℕ) := (buyKnots k j t).choose
private def knotCost (k : ℝ) (j t : ℕ) := (buyKnots k j t).choose_spec.choose
abbrev firstCard := (Fintype.card (TypeFace 1):ℝ)
abbrev secondCard := (Fintype.card (TypeFace 2):ℝ)

def towerPrice (k : ℝ) (P : MapPrices) (i j : ℕ) :=
  (firstCard * P.Ω i + ((secondCard * P.Ω i) * (secondCard * P.Ω i) * (secondCard * P.Ω j))) + (1+secondCard*knotCost k i j)
variable (P : MapPrices) (k : ℝ) (i j : ℕ)
private lemma knotted_fees_pos (k : ℝ) (i j) : 0 ≤ knotCost k i j := (buyKnots k i j).choose_spec.choose_spec.2.1.le
lemma basic_fees {P} (hp : 0 ≤ P.Ω i) (hP : 0 ≤ P.Ω j) :
    firstCard*P.Ω i ≤ towerPrice k P i j ∧ (secondCard*P.Ω i)*(secondCard*P.Ω i)*(secondCard*P.Ω j) ≤ towerPrice k P i j ∧ secondCard*knotCost k i j ≤ towerPrice k P i j := by
 unfold towerPrice
 -- correct order: towerPrice used fine i and coarse j but def pre terms? fix
 have h₁ : 0≤firstCard := Nat.cast_nonneg _
 have h₂ : 0≤secondCard := Nat.cast_nonneg _
 have ht := knotted_fees_pos k i j
 constructor
 · apply le_trans _ (le_add_of_nonneg_right (by positivity)); exact le_add_of_nonneg_right (by positivity)
 constructor
 · exact le_trans (le_add_of_nonneg_left (mul_nonneg h₁ hp)) (le_add_of_nonneg_right (by positivity))
 exact le_trans (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_left (by positivity))

end gifts

variable {G : Gauge} {c f : Side} (S : StepData c f)
lemma frame_color (i j : ℕ) (A : Matrix (Body i f) (Body j c) ℝ) (v : fieldDir G c j) (b) : parts G i (actionFrame A v) b=A*ᵥ(parts G j v b) := by
   funext z; let g : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj b) (WithLp.linearEquiv 2 ℝ _).toLinearMap
   change g (∑ x,_)=∑ x,_
   rw [map_sum]; exact Finset.sum_congr rfl fun x _=>map_smul g _ _
lemma frame_knock {α : Type*} [Fintype α] (a : Matrix (Body 2 f) α ℝ) (v : α→G.Color) (i e) : parts G 2 (actionFrame a v) i e = (a*ᵥ(fun x=>v x i)) e := by
  let l : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj i) (WithLp.linearEquiv 2 ℝ _).toLinearMap
  change l (∑ x,_)=∑ x,_; rw [map_sum]; exact Finset.sum_congr rfl fun x _=>map_smul l _ _
lemma frame_ext {n : Side} {k} {v w : fieldDir G n k} (h : ∀ a,parts G k v a=parts G k w a) : v=w := funext fun i=> (WithLp.linearEquiv 2 ℝ _).injective <| funext fun j=> congr_fun (h j) i

set_option maxHeartbeats 400000 in
lemma cleanIdentity {H H' T} (h : Towers.Diagonal S H H' T) {p η C} (hH : Floor H p f η C) (v : Dir G c) :
    dColor G f 1 (polish (installed S.ratio T.A0) v)=actionFrame ((H.dual_diag.acts f) * (installed S.ratio T.T) * H'.diagonal.acts c) (dColor G c 1 v) := by
  apply frame_ext; intro a
  rw [frame_color 2 2]
  let w := parts G 1 v a
  let Df := H.dual_diag.acts f
  let TT := installed S.ratio T.T
  let Hc := H'.diagonal.acts c
  let Hf := H.diagonal.acts f
  let TF := installed S.ratio T.A0
  change d 1 f *ᵥ (TF *ᵥ w) = (Df * TT * Hc) *ᵥ (d 1 c *ᵥ w)
  rw [mulVec_mulVec, mulVec_mulVec]
  apply congr_arg (· *ᵥ w) _
  have hd : Df * Hf=1 := Matrix.mul_eq_one_comm.mp hH.diagonalInv
  calc
    d 1 f * TF = Df * Hf * d 1 f * TF := by rw [hd,Matrix.one_mul]
    _ = Df * (Hf * d 1 f * TF) := by simp_rw [Matrix.mul_assoc]
    _ = _ := by rw [show Hf*d 1 f*TF=TT*Hc*d 1 c from h.stays.symm]; simp_rw [Matrix.mul_assoc]

def deltaV {n : Side} (s : Axis) (v : Dir G n) : fieldDir G n 2 := actionFrame (Next.Free.motion _ n [s]) (dColor G n 1 v)
def gradD {n : Side} (v : Dir G n) := ‖(deltaV · v : Axis→fieldDir G n 2)‖
lemma delta_entry (s : Axis) {n : Side} (v : Dir G n) i : deltaV s v i = ((dColor G n 1 v) (i.1+step s, i.2) - dColor G n 1 v i) := by
  apply (WithLp.linearEquiv 2 ℝ _).injective; ext1 j
  exact Eq.trans (congr_fun (frame_color 2 2 (Next.Free.motion (TypeFace 2) n [s]) (dColor G n 1 v) j) i) <|
     (by rw [motion_walk,motion_zero,mul_one,knock_entry]; rfl)

variable {A : Levels G} (P : MapPrices) (M : Horizon A) {hM : M.Suffices P} {l : ℕ→ℕ→ℝ}
def Figure (P : MapPrices) (A : Levels G) (M : Horizon A) (l : ℕ→ℕ→ℝ) : Prop := (∀ N m, m≤N → Next.Free.Defined A.clock.kernel.penalty (l N m) (location A N m) (M.H N m)) ∧
    (∀ N m,m<N → (M.towers N m).A0= (Flight.duo A.clock.kernel.penalty (destination A N m)).A0 ∧ (M.towers N m).T=(Flight.duo A.clock.kernel.penalty (destination A N m)).T)

noncomputable def selectedMatrix (A : Levels G) (M : Horizon A) (i N p : ℕ) := installed (A.clock.op N p).ratio (M.towers i N).A0

include hM
set_option maxHeartbeats 400000 in
lemma cost_one (L : ℕ) (m p) (hmi : m < L) (v : Dir G (A.S.side m p)) (T : Figure P A M l) :
    let y := polish (selectedMatrix A M L m p) v
    let i := A.clock.J (m+1); let j := A.clock.J m
    let h := (A.S.block m).val
    let D := towerPrice A.clock.kernel.penalty P i j
    ‖y‖ ≤ (D/(h:ℝ))*‖v‖ ∧ ‖dColor G _ 1 y‖ ≤ (D/(h:ℝ)^2)*‖dColor G _ 1 v‖ ∧ gradD y ≤ (D/(h:ℝ)^3)*gradD v := by
 intro y i j h D
 let S:=A.clock.op m p
 let H := M.towers L m; let Hf := M.H L (m+1); let Hc := M.H L m
 let ℓ := (((A.S.block m).val : ℕ) : ℝ)
 have hz : ℓ=h := rfl
 have he (m : ℕ) : m≤L → 0≤P.Ω (A.clock.J m) := by
   intro hm
   have hf := (hM.rows L m hm).1 (plaquette ((⟨(0,1),by decide⟩ : PlaqAxes))) (plaquette ((⟨(0,1),by decide⟩ : PlaqAxes)))
   exact (tsum_nonneg hf.1).trans hf.2.2
 have hp := basic_fees (i:=i) (j:=j) (P:=P) A.clock.kernel.penalty (he (m+1) hmi) (he m hmi.le)
 have hD : 0≤D := le_trans (mul_nonneg (Nat.cast_nonneg _) (he _ hmi)) hp.1
 have hp' : 0 < ℓ := Nat.cast_pos.mpr ((by positivity : 0 < (A.S.block m).val))
 
 have hL : S.ratio.count.val=h := rfl
 have hYA : WideBudget (selectedMatrix A M L m p) (D / h) := fun z=> (cross_zero _ ((hM.costs L m hmi).2.2.2 [] (Nat.zero_le _)|>.1) (P.alpha_pos i).le z).trans (by rw [List.length_nil,add_zero,pow_one]; change firstCard * (P.Ω i/ ℓ) ≤ D/ℓ; rw [←mul_div_assoc]; exact div_le_div_of_nonneg_right hp.1 hp'.le)
 have hClean := cleanIdentity (G:=G) S (hM.crossings L m p hmi) (hM.all L (m+1) hmi (A.S.side (m+1) p))
 have hF := T.1 L (m+1) hmi; have ht := T.1 L m hmi.le; rcases T.2 L m hmi with ⟨hA,hT⟩
 let Z := destination A L m
 let C : Matrix (Body 2 (A.S.side (m+1) p)) (Body 2 (A.S.side m p)) ℝ := (Hf.dual_diag.acts _) * installed S.ratio H.T * (Hc.diagonal.acts _)
 have hC' : C = installed (Z.visitRatio S.sizes) (Flight.psi A.clock.kernel.penalty Z) := by
   rw [Flight.psi_bridge A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm _) Z S.sizes]; change ((M.H L (m+1)).dual_diag.acts _)*(_)*_=(_)*(_)*_; rw [hT, hF.dual, ht.diag, loc_land A L m hmi]; rfl
 have hC : dColor G _ 1 y=actionFrame C (dColor G _ 1 v) := hClean v
 have hcb : WideBudget C (D / ℓ^2) := by
   let q := (installed S.ratio H.T)
   have h₁ : WideBudget q (Fintype.card (TypeFace 2)*(P.Ω i/ℓ^2)) := cross_zero _ (((hM.costs L m hmi).2.2.2 [] (Nat.zero_le _)).2) (P.alpha_pos i).le
   have h₂ := wide_mul h₁ (row_zero ((hM.rows L m hmi.le).1) (P.alpha_pos j).le _) (show 0≤secondCard * P.Ω j from mul_nonneg (Nat.cast_nonneg _) (he _ hmi.le)) -- rows first .diagonal yes
   have h₃ := wide_mul (row_zero ((hM.rows L (m+1) hmi).2.2.2.2) (P.alpha_pos i).le _) h₂ (by positivity [he _ hmi.le,he _ hmi])
   exact fun a => le_trans (b:=(secondCard*P.Ω i)*(secondCard*(P.Ω i/ℓ^2)* (secondCard*P.Ω j))) (by rw [show C=Hf.dual_diag.acts _ * (q * (M.H L m).diagonal.acts _) from Matrix.mul_assoc ..]; exact h₃ a) (by change (secondCard*P.Ω i)*(secondCard*(P.Ω i/ℓ^2)* (secondCard*P.Ω j)) ≤ _; rw [show (secondCard*P.Ω i)*(secondCard*(P.Ω i/ℓ^2)* (secondCard*P.Ω j))= (secondCard * P.Ω i)*(secondCard * P.Ω i)*(secondCard * P.Ω j) / ℓ^2 by ring]; exact div_le_div_of_nonneg_right hp.2.1 (by positivity))
 have hδ : ∀ s:Axis, deltaV s y= actionFrame (installed S.ratio (Flight.groundPsi A.clock.kernel.penalty Z [s])) (deltaV s v) := by
    intro s
    have ht := Flight.refund_period A.clock.kernel.penalty A.clock.kernel.penalty_pos (A.clock.adm m) Z S.sizes [s] (show List.length [s] ≤ i-2 from by have h:=A.clock.adm (m+1); change 4 ≤ i at h; change 1≤_; omega)
    unfold deltaV; rw [hC]; apply frame_ext; intro a
    rw [frame_color 2 2,frame_color 2 2,frame_color 2 2,frame_color 2 2,mulVec_mulVec,mulVec_mulVec,hC',ht]
    rfl
 constructor
 · change ‖polish _ _‖ ≤ _; rw [polish_eval]; exact frame_pay v hYA (show _ from div_nonneg hD hp'.le)
 constructor
 · rw [hC]; exact frame_pay _ hcb (by positivity)
 change ‖(deltaV · y: Axis→ fieldDir G _ 2)‖ ≤ _
 refine (pi_norm_le_iff_of_nonneg (by unfold gradD; positivity)).mpr fun a=>?_ ; rw [hδ]
 have hc := ((buyKnots A.clock.kernel.penalty i j).choose_spec.choose_spec)
 have hv := (frame_pay (deltaV a v) (cross_zero S.ratio (K:=Flight.groundPsi A.clock.kernel.penalty Z [a]) (show Row.strip _ (knotWidth A.clock.kernel.penalty i j) (knotCost A.clock.kernel.penalty i j/ ℓ^3) from hc.2.2 Z [a] (A.clock.adm (m+1)) (A.clock.adm m) A.clock.kernel.penalty_pos (by change 1 ≤ i-2; have h:=A.clock.adm (m+1); change 4 ≤ i at h; omega)) hc.1.le) (mul_nonneg (Nat.cast_nonneg (Fintype.card (TypeFace 2))) (div_nonneg hc.2.1.le (by positivity))))
 apply hv.trans (mul_le_mul (by change (secondCard:ℝ)* (_ / ℓ^3) ≤ D/ℓ^3; rw [←mul_div_assoc]; exact div_le_div_of_nonneg_right hp.2.2 (by positivity)) (norm_le_pi_norm (deltaV · v) a) (norm_nonneg _) (by positivity))
end YM.UVExt.Paths

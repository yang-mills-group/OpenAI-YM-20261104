import YM.FormalBulk08.Flat.Repack

/-!
The redundant centered law's precision and inverse on all side lengths.
The auxiliary chart here is just to make a momentum-measured gap argument,
and the redundancy must still be removed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary
open scoped Topology BigOperators Matrix
variable {G : Gauge} {j t : ℕ}

abbrev primary (P : Patch) (K : KernelChoices) (c : Side) : StepData c (c*P.L) := ⟨P,K,rfl⟩
lemma chooseable (c f : Side) (S : StepData c f) : Nonempty S.Choices := by
    unfold StepData.Choices StepData.SitesChoice StepData.BondChoice Patch.FrameTag; infer_instance

def meat {c f : Side} (S : StepData c f) (t : S.Choices) (V : Train j) : Matrix (Bodies G c f) (Bodies G c f) ℝ :=
    let M:=butt G c f; let N:=fortune G S; let W:=postroom (G:=G) S t (Stationary.inch S.patch.L)
    Mᵀ*patron G (Precision.K ((pink S.kernel.penalty V).acts f))*M + S.kernel.penalty • (Nᵀ*N) + Wᵀ*W

def device (P : Patch) (K : KernelChoices) (c : Side) (t : (primary P K c).Choices) (V : Train j) :=
    let T:=clothe G (primary P K c); repackM T T (meat (G:=G) (primary P K c) t V)

lemma pre_meter {B : Patch} {K : KernelChoices} (c : Side) (U : Train j)
    (t : (primary B K c).Choices) (Y : After K.penalty U) (h : B.Branches K G) (D σ : ℝ) (he : Y.B.metric.strip σ D) (hp : 0<σ) :
    Jaunt (approached (device (G:=G) B K c t U)) (forceK G B (shutter G B) K.penalty Y.B) 0 := by
  let S:=primary B K c
  have hv : Stationary.inch S.patch.L * σ ≤ σ := mul_le_of_le_one_left hp.le (Stationary.inch_le _)
  have hx := meters S t h Y.B D σ (strip_mono he hv le_rfl) hp
  change Jaunt (approached (repackM (clothe G S) (clothe G S) (meat (G:=G) S t U))) _ _
  have hp : let W:=postroom (G:=G) S t (Stationary.inch S.patch.L); meat (G:=G) S t U=frontR G S Y.B + Wᵀ*W := by
    intro W
    unfold meat frontR posting
    rw [Y.stands]
  rw [hp]; exact hx
open scoped Classical

def Clerk (G : Gauge) (P : Patch) (K : KernelChoices) (V : Train j) (U : Row (ParcelG G P.L) (ParcelG G P.L)) :=
    ∀ c : Side, ∀ t : (primary P K c).Choices, (device P K c t V)*(U.acts c)=1

lemma unique_clerk {V : Train j} {K : KernelChoices} (P : Patch) {A B : Row (ParcelG G P.L) (ParcelG G P.L)}
    (h : Clerk G P K V A) (g : Clerk G P K V B) (ha : A.safe) (hb : B.safe) : A=B := by
  apply bank_injective ha hb; intro c
  let t : (primary P K c).Choices := Classical.choice (chooseable ..)
  exact left_inv_eq_right_inv (mul_eq_one_comm.mp (h c t)) (g c t)

/-- Power moments arbitrary at fixed admission, since the center cost is
exponential. Hard point is `η` given *before* a patch. -/
theorem center_price (G : Gauge) (K : KernelChoices) (j : ℕ) (hj : 4≤j) :
    ∃ η : ℝ, 0<η ∧ ∀ P : Patch,P.J=j → P.Branches K G → ∃ C : ℝ,0<C ∧
      ∀ V : Train j, ∃ U : Row (ParcelG G P.L) (ParcelG G P.L), Clerk G P K V U ∧ U.strip η C := by
  let k:=K.penalty
  obtain ⟨σ,A,ε,hσ,hA,hε,a,h⟩:=affiliates _ hj k K.penalty_pos
  obtain ⟨w,D,hw,hS,hd,H⟩:=watches K j G _ _ _ hσ hε hA.le
  let η:=w/3
  have hη : 0<η:=by unfold η; positivity
  refine ⟨η,hη,fun P hP hp=>?_⟩
  obtain ⟨B,hB,hx⟩:=freezing G P w D hd
  let C:=B*(2*((1+η)/η))^4
  have hC : 0<C:=by unfold C; positivity
  refine ⟨C,hC,fun V=> ?_⟩
  obtain ⟨W,hW,hh⟩:=h V
  let X := forceK G P (shutter G P) k W.B
  obtain ⟨ht,hT⟩:= H P hP hp W.B hW _ hh
  have hej := hx X ht hT
  have hv (q : Momentum) (hq : star q=q) : (X (-q))ᵀ=(X q)ᴴ := judge walentes
      (fun i=> pre_meter (walent i) V (Classical.choice (chooseable ..)) W hp A σ hW hσ) ht hw hq
  obtain ⟨hr,hF⟩:=delivers B w hw X ht hT.period hej hv
  let U:=record fun p=> (X p)⁻¹
  refine ⟨U,fun c t=>?_,hr⟩
  convert! inverse_rows c (device P K c t V) (fun p => hT.period (mon p) (Work.F07.realStrip _ hw (real_frequency _))) (pre_meter c V t W hp A σ hW hσ) (Row.rights η C hr hη.le) (fun p=> hF _ (mon_mem c p)) using 1
  congr
  exact Subsingleton.elim ..
end YM.FormalBulk08.Flat

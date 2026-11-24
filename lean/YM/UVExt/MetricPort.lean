import YM.UVExt.JetRays
import YM.UVExt.JetCost

/-! Simultaneous all-period fidelity to the cover convolution. The price of absolute inclusive width moments is still needed later by the schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Wilson Precision Lattice Laurent Exterior Bid Filter Real Set Matrix Bloch Next.Free
open scoped ContDiff Topology Classical BigOperators
variable {σ D Γ : ℝ}

open Next.Free.UV Work.F08

lemma slot_top : Tendsto SlotSize cofinite atTop := by
  apply tendsto_atTop.mpr; intro b
  obtain ⟨m,hm⟩ := exists_nat_ge b
  let v := {s : Slot| s.walk.length ≤ m}
  have hv : Finite v := by
    letI : Finite {s:Walk|s.length ≤ m} := (limited_walks m).to_subtype
    letI : Finite PlaqAxes := Finite.of_injective Subtype.val Subtype.val_injective
    exact Finite.of_injective (fun p:v=> ((⟨p.val.walk,p.property⟩ : {s:Walk|s.length≤m}),p.val.plaq))
       fun a c h=> Subtype.ext (by have h1 := congr_arg (fun p : {s:Walk|s.length≤m}×PlaqAxes => p.1.val) h; have h2 := congr_arg Prod.snd h; rcases a with ⟨⟨x,y⟩,hx⟩; rcases c with ⟨⟨z,t⟩,hz⟩; exact congr_arg₂ Slot.mk h1 h2)
  apply eventually_cofinite.mpr (show _ from (show v.Finite from Set.finite_coe_iff.mpr hv).subset fun i he=> ?_) -- replace
  exact (show i.walk.length ≤ m from by apply Nat.cast_le (α:=ℝ)|>.mp; exact (Nat.cast_le.mpr (Nat.le_add_right ..) : (i.walk.length:ℝ) ≤ SlotSize i).trans (by exact (lt_of_not_ge he).le.trans hm))

lemma pool_convergence {α β : Type*} (s : α→β) {f : ℕ→α→ℝ} {L : α→ℝ} (hL : Tendsto L cofinite atTop) {Z : α→ℝ} (hf : Tendsto f atTop (𝓝 Z)) (he : 0<σ) (hh : ∀ᶠ i in atTop,Carries D σ L (f i)) : Tendsto (fun n=> pool (f n) s) atTop (𝓝 (pool Z s)) := by
  classical
  refine tendsto_pi_nhds.mpr fun d=>?_
  let W x := if s x=d then (1:ℝ) else 0
  have hd (x : α) : ContDiff ℝ ω (fun (_:ℝ)=> W x) := contDiff_const
  have ht := weigh_pass (h:=fun x (_:ℝ)=>W x) (W:=Z) 1 0 L (by norm_num) le_rfl (fun _=>contDiff_const) (fun i t n b he=>?_ ) he f hf hh 0 (0:ℝ) hL -- W name? Z
  · simpa only [iteratedDeriv_zero,pool_mask, W,mul_ite,mul_one,mul_zero] using ht
  cases b with
  | zero => unfold W; rw [iteratedDeriv_zero,pow_zero,mul_one]; change ‖(if s t=d then (1:ℝ) else 0)‖ ≤ 1; split <;> norm_num
  | succ b => simp [iteratedDeriv_const]

private lemma mat_mul_limit {a b c : Type*} [Fintype b] {X : ℕ→Matrix a b ℝ} {Y : ℕ→Matrix b c ℝ} {A B}
    (h : Tendsto X atTop (𝓝 A)) (hp : Tendsto Y atTop (𝓝 B)) : ∀ i j, Tendsto (fun k=>(X k*Y k) i j) atTop (𝓝 ((A*B) i j)) := fun i j=>
   tendsto_finsetSum _ fun z _=> (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) z).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp z) j)

/-- hypothetical roots determined by infinite path coefficients. -/
def groundBed {G : Gauge} (W : Shadow G) : Bed := ⟨(fun _ _ _=>0), (fun _ _ _=>0), (fun _ _ _=>0), (fun _ _ _=>0), fun i j d => pool (W.row (plaqEquiv.symm i)) placeSlot (d,plaqEquiv.symm j)⟩
lemma ground_ties {G : Gauge} (W : Shadow G) b d k: pool (W.row b) placeSlot (d,k) = (groundBed W).roots (plaquette b) (plaquette k) d := by
  change pool (W.row b) placeSlot _ = pool (W.row (plaqEquiv.symm (plaqEquiv b))) placeSlot (_,plaqEquiv.symm (plaqEquiv k)); rw [plaqEquiv.symm_apply_apply, plaqEquiv.symm_apply_apply]

def bedFull {G : Gauge} (W : Shadow G) (p : Clip) (n : Side) := (groundBed W).full p n
namespace Passing
variable {G : Gauge} {M : ℕ→PathData G} {C Λ : ℝ} {W : Shadow G} {p : Clip} (hp : Passing M W σ C Λ p)
include hp
lemma roots_limit {H : ℕ→Bed} (h : ∀ᶠ i in atTop,Attached (H i) (M i)) : Tendsto (fun i=> (H i).roots) atTop (𝓝 (groundBed W).roots) := by
  refine tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=>tendsto_pi_nhds.mpr fun x=>?_
  let a' := plaqEquiv.symm a; let b' := plaqEquiv.symm b
  exact ((tendsto_pi_nhds.mp (pool_convergence placeSlot slot_top (hp.row a') hp.width (hp.mask.mono fun i hi=>(shadow_pay (M i) hi).row a')) (x,b')).congr' <| (h.and hp.mask).mono (fun i hi=>Eq.trans (layout_row _ _ hi.1 hi.2 (a:=a') (b:=b') x) (by unfold a' b'; rw [show ∀ a, plaquette (plaqEquiv.symm a)=a from plaqEquiv.apply_symm_apply, show plaquette (plaqEquiv.symm b)=b from plaqEquiv.apply_symm_apply _])))
lemma full_limit {H : ℕ→Bed} (h : ∀ᶠ i in atTop,Attached (H i) (M i)) {δ Γ} (hδ : 0<δ) (hr : ∀ᶠ i in atTop,(H i).roots.strip δ Γ) (n : Side) : Tendsto (fun i=> (H i).full p n) atTop (𝓝 (bedFull W p n)) := by
  have hv := tendsto_entries (hp.roots_limit h) hδ hr n
  refine tendsto_pi_nhds.mpr fun ⟨a,b⟩=> tendsto_pi_nhds.mpr fun i=> ?_
  cases b with
  | inl b => exact tendsto_const_nhds
  | inr b => exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv (a,b)) i
end Passing

private lemma any_pledge {G : Gauge} (V : Levels G) (N m : ℕ) (k l : ℝ) (hk : 0<k) (n : Side) :
    let B := blue k (location V N m)
    let X := d 2 n * B.acts n
    (pledge k l (location V N m)).acts n = B.acts n + l • (X.transpose*X) := by
     intro B X; let hX := billed_drawer k hk (V.clock.adm m) (fun x : Unit=> location V N m) |>.whole ()
     let hb := (heart_saves k hk (V.clock.adm m) (fun x : Unit=> location V N m)).2.whole ()
     have hh := Whole.boundary 2
     have hxx : (drawer k (location V N m)).acts n=X := hh.acts hb n
     unfold pledge; rw [hb.acts_plus ((hX.flipped.prod hX).weight _) n,acts_scale,hX.flipped.acts hX,acts_trans,hxx]

section metrics
variable {G : Gauge} {V : Levels G} {m : ℕ} {k l : ℝ}
lemma pledge_limits (hk : 0<k) (n : Side) : ∃ Y, Tendsto (fun d=> (pledge k l (location V d m)).acts n) atTop (𝓝 Y) := by
  have hx := slate_limit V n hk (m:=m)
  let B := (blueInf V n k m).map Complex.re
  have hX : Tendsto (fun d=> (blue k (location V d m)).acts n) atTop (𝓝 B) := tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b=>hx a b
  let W (d:ℕ) := Exterior.d 2 n * (blue k (location V d m)).acts n; let X := Exterior.d 2 n * B
  have hi : Tendsto W atTop (𝓝 X) := tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr <| mat_mul_limit (tendsto_const_nhds (x:=Exterior.d 2 n)) hX a
  have ht : Tendsto (fun i=>(W i).transpose*W i) atTop (𝓝 (X.transpose*X)) := tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=> mat_mul_limit (tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi j) i) hi a b
  refine ⟨B + l • (X.transpose*X), tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mpr fun b=> ?_⟩
  change Tendsto (fun i : ℕ=> (pledge k l (location V i m)).acts n a b) atTop (𝓝 (B a b + l * (X.transpose*X) a b))
  exact ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hX a) b).add ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht a) b).const_mul l)).congr fun i => congr_arg (fun y=>y a b) (any_pledge V i m k l hk n).symm

/-- Universal-period data of the *same* M sequence, no period-dependent reselection during comparisons. -/
structure Harbor (V : Levels G) (m : ℕ) (k l : ℝ) (H : ℕ→Bed) (M : ℕ→PathData G) (p : Clip) : Prop where
   ties : ∀ᶠ i in atTop, Attached (H i) (M i)
   full : ∀ n, ∀ᶠ i in atTop,∃ a b,Floor (H i) p n a b
   spend : ∃ δ Γ, 0<δ ∧ ∀ᶠ i in atTop,(H i).roots.strip δ Γ
   precision : ∃ g : ℕ→ℕ, Tendsto g atTop atTop ∧ ∀ᶠ i in atTop,(H i).inverse=pledge k l (location V (g i) m)
   positive : 0 < k
   symmetry : ∀ p, ∀ᶠ i in atTop, Sworn (H i) (V.S.side m p) G
namespace Harbor
variable {H H' : ℕ→Bed} {M M' : ℕ→PathData G} {p : Clip}
   (h : Harbor V m k l H M p)
include h
lemma subseq {g : ℕ→ℕ} (hg : Tendsto g atTop atTop) : Harbor V m k l (H ∘ g) (M ∘ g) p :=
  ⟨hg.eventually h.ties,fun n=>hg.eventually <| h.full n,by obtain ⟨δ,Γ,he,hδ⟩ := h.spend; exact ⟨δ,Γ,he,hg.eventually hδ⟩,
     by obtain ⟨r,hr,hM⟩ := h.precision; exact ⟨r∘g,hr.comp hg,hg.eventually hM⟩,h.positive,fun j=>hg.eventually <| h.symmetry j⟩
variable {W X:Shadow G} {σ C Λ σ' C' Λ' : ℝ} (hT : Passing M W σ C Λ p)
include hT
lemma acts (n: Side) : Tendsto (fun i=> (H i).metric.acts n) atTop (𝓝 ((bedFull W p n).transpose* (bedFull W p n))) := by
  obtain ⟨δ,Γ,hδ,hR⟩ := h.spend
  have hU := Passing.full_limit hT (h.ties) hδ hR n
  have hf := (h.full n).mono fun i hi => hi.choose_spec.choose_spec.roots -- wrong choose nested
  have hQ : Tendsto (fun i=> H i |>.full p n |>.transpose) atTop (𝓝 (bedFull W p n).transpose) := tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hU b) a
  exact ((show Tendsto (fun i=> _) atTop (𝓝 _) from tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=>mat_mul_limit hQ hU a b).congr' hf)
lemma same_acts {H'} (h' : Harbor V m k l H' M' p) (ht : Passing M' X σ' C' Λ' p)
    (n: Side) : (bedFull W p n).transpose* (bedFull W p n) = (bedFull X p n).transpose* bedFull X p n := by
  obtain ⟨Z,hZ⟩ := pledge_limits (V:=V) (m:=m) (l:=l) h.positive n
  have hinv {M' H} (h : Harbor V m k l H M' p) : Tendsto (fun i=> (H i).inverse.acts n) atTop (𝓝 Z) := Exists.elim h.precision fun g ⟨hg,hH⟩ => (hZ.comp hg).congr' (hH.mono fun i hi=> congr_arg (fun H=>H.acts n) hi.symm)
  have hf := (tendsto_pi_nhds (f:= fun i=>(H i).metric.acts n * (H i).inverse.acts n)).mpr fun a=> tendsto_pi_nhds.mpr fun b=>mat_mul_limit (h.acts hT n) (hinv h) a b
  have hr := tendsto_const_nhds (x:=(1 : Matrix (Body 2 n) (Body 2 n) ℝ)).congr' (f₂:=fun i=>(H i).metric.acts n * (H i).inverse.acts n) ((h.full n).mono fun i hi=>by obtain ⟨a,b,h⟩ := hi; exact h.inverse.symm)
  let A := (bedFull W p n).transpose * bedFull W p n
  let B := (bedFull X p n).transpose*bedFull X p n
  have ia : A*Z=1 := by ext i j; exact tendsto_nhds_unique (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf i) j) ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hr i) j))
  have hr' := tendsto_const_nhds (x:=(1 : Matrix (Body 2 n) (Body 2 n) ℝ)).congr' (f₂:=fun i=>(H' i).metric.acts n * (H' i).inverse.acts n) ((h'.full n).mono fun i hi=>by obtain ⟨a,b,h⟩ := hi; exact h.inverse.symm)
  have ib : B*Z=1 := by
    ext i j
    exact tendsto_nhds_unique (mat_mul_limit (h'.acts ht n) (hinv h') i j) (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hr' i) j)
  change A=B; calc
     _ = A*(Z*B) := by rw [mul_eq_one_comm.mp ib,mul_one]
     _ = _ := by rw [← mul_assoc,ia,one_mul]
end Harbor
end metrics

end YM.UVExt.Paths

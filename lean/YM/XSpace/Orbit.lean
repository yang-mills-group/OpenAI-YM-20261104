import YM.XSpace.Gathering

/-!
# A color orbit theorem at fixed d for Maxwell Wick labels

A-priori no smooth selection at all is implied. Every REAL move preserving the
measuring arrays, and meeting the lower-grade forced orientations, is on an orthogonal
orbit on color alone. Singlet images may move; their infinitesimal constraints are in a
subsequent file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory MvPolynomial Maxwell Maxwell.Free
open Next.Rank.Normal Legs
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff

variable {G : Gauge} {d : ℕ} {R : WickPol G → WickPol G}

def RealMove (R : WickPol G→ WickPol G) (d : ℕ):Prop:=∀ p∈shellSector G d,realForm p=p→ realForm (R p)= R p
def Rot (M : Motor G) : Prop:=∀ x:G.Color,‖M x‖=‖x‖

lemma real_val {p:WickPol G} (hp : realForm p=p) (T:TaylorTower G): (((probe T p).re:ℝ):ℂ)=probe T p:=by
  have he:= real_eval p T; rw [hp] at he; apply Complex.ext; rfl; have hK:= congr_arg Complex.im he; simp at hK; change 0=_; linarith

lemma pump_cont : Continuous (pump (G:=G)):=by
  let D : Fabric G →ₗ[ℝ] Motor G :=
    { toFun:= pump
      map_add' a b:=by
        ext x i; change ⟪x,row (a+b) i⟫= _ + _; rw [show row (a+b) i=row a i+row b i by rfl,inner_add_right]; rfl
      map_smul' t a:=by ext x i; change ⟪x,row (t • a) i⟫=t*_; rw [show row (t • a) i=t • row a i by rfl,real_inner_smul_right]; rfl }
  exact D.toContinuousLinearMap.continuous

lemma exists_wrench (C₀ : G.ColorIndex) (K : Moves R d) (hg : RealMove R d) (hd : 4≤d):
    ∃ M : Motor G, (∀ T:TaylorTower G,∀ p∈shellSector G d,realForm p=p→probe T (R p) = probe (motor M T) p) ∧ Rot M:=by
  let I:= TaylorTower G × {p:WickPol G//p∈shellSector G d ∧ realForm p=p}; let v:= plank (1:Motor G); let r:=‖v‖+1
  let f (R: WickPol G→WickPol G) (i:I) (M : Fabric G):= (probe (motor (pump M) i.1) (R i.2.val)).re
  have he p i: Continuous (f p i):= Complex.continuous_re.comp ((travel_smooth ..).continuous.comp pump_cont)
  have hh (i:I) (v : Fabric G): ((f id i v:ℝ):ℂ)=probe (motor (pump v) i.1) i.2.val :=real_val i.2.property.2 _
  have hf (i:I) (v : Fabric G): ((f R i v:ℝ):ℂ)=probe (motor (pump v) i.1) (R i.2.val) :=real_val (hg i.2.val i.2.property.1 i.2.property.2) _
  have HB: Gather.Match (f id) (f R) r:= by
    intro n i
    have hz:= moment_agreement K C₀ (fun a:Fin n=> (i a).2.val) r 0 (fun a=> (i a).1) (fun a=> (i a).2.property.1) hd
    simp_rw [← hh (i _),← hf (i _),← Complex.ofReal_prod,Complex.real_smul, ← Complex.ofReal_mul,integral_complex_ofReal] at hz; exact Complex.ofReal_injective hz
  obtain ⟨M,hM,h⟩:= Gather.realizes (f id) (f R) HB (he id) (he R) v (show ‖v‖<r from lt_add_one _)
  have H (T) (p) (hp:p∈shellSector G d) (hp':realForm p=p): probe T (R p)=probe (motor (pump M) T) p:= by
    let i:I:= (T,⟨p,hp,hp'⟩); have hx:=hf i v; rw [← h,hh, show pump v=1 from able 1, motor_one] at hx; exact hx.symm
  refine ⟨pump M,H,fun x=>?_⟩
  let a:=cell 0 1; let p:=team G a a; let T:TaylorTower G:= Pi.single (M:=fun i=> Shell G i) 0 (fill 0 x (blade 0 1 (1:ℝ)))
  have hx : available (T 0) a=x:=by unfold T; rw [Pi.single_eq_same,fill_g]; norm_num [a,cell_price,wedge,Matrix.one_apply]
  have hk := H T p (team_label _ _ hd) (realTeam ..); unfold p at hk; rw [K.quad a,basicTeam,basicTeam,shades,hx,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hk
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp (Complex.ofReal_injective hk)).symm
end YM.XSpace.Sample

import YM.RGComparison.Core16.Spool.Proof
/-! # Public endpoint (weighted pressure cost BEFORE period choice). Two-currency of real
   marker integrals and perturbative Wick-monials. NOT transferred outputs past this step.
Registered proliferation burns Warp horizon here as needed. Uses all points and the same V in the
whole polynomial before orientation reads. Calling correspondence needs the Chapter10 ancestor,
still must pay future consumption separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Spool
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Lumen Lumen.Planet Parcel Parcel.Oven Next.Fluctuations Finset Complex Analysis
open Lumen.Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {κ:ℝ} {ι:Type}[Fintype ι] {c f : Side} (J:ι→Lamp G)
variable (S:StepData c f) (T:Forest S.ratio){P: Oven S.patch}(X:P.Form G)(Z:ChartRatio G)(u:Directions G c) (p:ι→Site f) (b:Bool)

-- Re/Im linked in one coefficient, before Theta measure movement.
def rankℝ := Fk.read (lens (S:=S) u X T) Z (earns S T J p) (look b ∘ sight J) (power J)
def rank (j:ℕ):ℂ:= ⟨rankℝ J S T X Z u p false j,rankℝ J S T X Z u p true j⟩
variable {S T X Z} {u} (hP:P.Offers X S.kernel)(he:Bid.Larger (G:=G) S)(hg : ∀ i,‖u i‖≤X.Q)
include he
lemma ice (T : Forest S.ratio) (g:ℝ) : look b (reads J S u p g) = Fk.baron (lens u X T) (echo S T J p b) (power J) g := by
    let I:= lens (S:=S) u X T; let M:=skillet G T.Free; let V:= slice u g
    unfold reads Fk.baron Planet.expect; rw [map_smul,map_smul,on_line J S u p T he.1,quiet S u T he.1,smul_eq_mul,smul_eq_mul]
    congr 1
    let v:=∫ x,(Hut.seam S T V).output g x∂M; let z:=Next.Fluctuations.Sector.prefactor S G (g^2)⁻¹; have hz:z ≠ 0:= (pow_pos (inv_pos.mpr (S.penaltyZ_pos ..)) _).ne'
    let w:=∫ x,(Hut.seam S T V).output g x * look b (column J p (T.drape x))∂M
    change (z*v)⁻¹*(z*w)=w/v; rw [←mul_div_mul_left w v hz,div_eq_mul_inv, mul_comm]

include hP hg
lemma forecast (T : Forest S.ratio) (hZ:LocalRatio Z) : Aspiration (fun g=> look b (reads J S u p g)) (rankℝ J S T X Z u p b):=by
    cases S with | mk S K D=>
    rw [show (fun g=> look b (reads J { patch:=S, kernel:=K, sizes:=D } u p g))=_ from funext (ice (X:=X) J p b he T)]
    obtain ⟨C,-,h⟩:= encouraging J
    apply Fk.exterior (P:=lens u X T) (paints T hP hg he) hZ (offers J (S:=_) (T:=T) p hP.good b (h b)) (painted J b) (sphere J b)

-- Economic solution independent reference sheet etc through all seam moments whenever both apertures admit.
omit hP in
lemma standard {P':Oven S.patch} {X':P'.Form G}{Z':ChartRatio G} (T T':Forest S.ratio)(hP:P.Offers X S.kernel) (hP':P'.Offers X' S.kernel) (hh:∀i,‖u i‖≤ X'.Q) (hz:LocalRatio Z) (hZ:LocalRatio Z') : rank J S T X Z u p = rank J S T' X' Z' u p:=by
    funext j
    apply Complex.ext
    · exact congr_fun ((forecast J p false hP he hg T hz).unique (forecast J p false hP' he hh T' hZ)) j
    exact congr_fun ((forecast J p true hP he hg T hz).unique (forecast J p true hP' he hh T' hZ)) j
omit hP hg he

-- Σ complex resplendent at requested order r. Geometry: every allowed real period & u small-g
-- *sup* aperture. All origins/census roots. Requests horizon before G and after X as declared.
structure Price (B:Lumen.Stage)(r:ℕ)(C:ℝ)(v:ℕ→ℂ)(f:ℝ→ℂ):Prop where
    growth (i:ℕ):i≤r→‖v i‖ ≤ C
    cost (g:ℝ):0<g → g ≤ dollar B.L → ‖f g - peval v r g‖ ≤ g^(r+1)*C
private lemma polar {V:ℂ} : ‖V‖ ≤ |look false V| + |look true V|:= by
    calc _ ≤ |V.re| + |V.im| := Complex.norm_le_abs_re_add_abs_im V
         _ = _ := by simp [look]
lemma boons {v:ℝ} {U:Lumen.Stage} {r:ℕ} (hp:∀b,Fk.Allots U (rankℝ J S T X Z u p b) r v (fun g=> look b (reads J S u p g))) : Price U r (2*v) (rank J S T X Z u p) (reads J S u p):= by
    let f:= rank J S T X Z u p; let M:= reads J S u p; have hw b : look b ∘ f = rankℝ J S T X Z u p b := funext fun x=> by cases b <;> simp [f,look,rank];
    constructor
    · intro i hi; refine polar.trans ((add_le_add ?_ ?_).trans_eq (two_mul v).symm)
      · exact ((congr_arg abs (show look false (f i)=_ from congr_fun (hw false) i)).le.trans ((hp false).front i hi))
      exact ((congr_arg abs (show look true (f i)=_ from congr_fun (hw true) i)).le.trans ((hp true).front i hi))
    intro g hg ht; let A:=peval f r g; have he b : look b A=_:= (WilsonXLocal.eval_map (look b) (a:=f) g).symm
    let s:= -Real.log g; have hG:dollar s=g:=by unfold dollar s; rw [neg_neg,Real.exp_log hg];
    have hd:U.L ≤ s:= by unfold dollar at ht; unfold s; linarith [Real.log_le_log hg ht,Real.log_exp (-U.L)]
    have hx b: |look b (M g - A)| ≤ g^(r+1)*v:=by
       rw [map_sub,he b,hw]; rw [← hG]; exact (hp b).earns _ hd
    exact polar.trans ((add_le_add (hx false) (hx true)).trans_eq (by ring))
variable {H:Patch}{K:KernelChoices}

/-- Q arbitrary positive, Oven from Pose picked even before stage geometry c,f.
    Keep it fixed (must also use in calling evaluation & restriction). -/
lemma every {P:Oven H}{X:P.Form G}(hp:P.Offers X K)(B:Lumen.Stage)(r:ℕ)(hZ:LocalRatio Z):∃ (U:Lumen.Stage)(C:ℝ), U.Above B∧ 0≤C ∧ ∀ (c f:Side)(hd:f.val=c.val*H.L.val),
     let S : StepData c f:=⟨H,K,hd⟩
     Bid.Larger (G:=G) S→∀ (T: Forest S.ratio)(u:Directions G c)(p:ι→ Site f),
       (∀ i,‖u i‖ ≤ X.Q)→ Price U r C (rank J S T X Z u p) (reads J S u p):=by
     obtain ⟨A,hA,hE⟩:= encouraging J
     obtain ⟨U,v,hU,hV,hv,H'⟩:= Fk.projection hZ hp.good B (fun i=> look i ∘ sight J) (sphere J) r (power J) (Fintype.card (Slice J)) hA
     refine ⟨U,2*v,hU,by positivity,?_⟩
     intro c f d S hs T u p he; apply boons J p
     intro b
     have hy: Fk.Allots U _ _ _ _:= H' T.Free (Hut.Rooms c f) S.Choices _ _ _ f (lens u X T) (paints T hp he hs) b (echo S T J p b) (earns S T J p) (offers J (S:=S) (T:=T) p hp.good b (hE b)) (painted J b)
     rw [show (fun g=> look b (reads J S u p g))=_ from funext (ice J p b hs T (X:=X) (u:=u))]; exact hy
end YM.RGComparison.Core16.Spool

import YM.Integration.FVA1Physical.Sources.Round2.ClipRows
import YM.Integration.FVA1Physical.Wilson.HaarPatch

/-! Exact identification of all forest-gauged absolute link logarithms on the
measured local portal, including the tree and every exterior link. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Set Metric Finset Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Bakery MSbar.Bakery.Film MSbar.Rolling MSbar.Lis
open Next.SectorChange YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)

theorem local_exp_log (x:G.Color) (small:‖x‖<(LocalH.geom_patch G).choose) :
    logWithin G (G.lieExp x)=x := by
  let key:=(LocalH.geom_patch G).choose
  have hit:x∈ball 0 key:=mem_ball_zero_iff.mpr small
  have near:G.lieExp x∈exponentialPatch G:=⟨x,hit,rfl⟩
  obtain ⟨_,_,inv,_,_,_,_⟩ := (LocalH.geom_patch G).choose_spec.2 key le_rfl
  rw [logWithin,Set.piecewise_eq_of_mem _ _ _ near]
  exact inv hit

theorem chartLog_stretch (g:ℝ) (v:Positions (Key F G))
    (small:∀ i:F.Free, ‖tint G _ v i‖<(LocalH.geom_patch G).choose) :
    chartLog g (Film.stretch F v)=g⁻¹ • Rolling.stamp F G v := by
  have one:logWithin G 1=0:=by
    have h:=local_exp_log (0:G.Color) (by simpa only [norm_zero] using (LocalH.geom_patch G).choose_spec.1)
    simpa only [G.mat_lieExp_zero] using h
  funext i
  obtain ⟨⟨x,a⟩,k⟩:=i
  let e:Edge (Site f):=(x,axisEquiv.symm a)
  change g⁻¹*(logWithin G (F.drape (fun j=>G.lieExp (tint G _ v j)) e)) k = g⁻¹*(if he:e∈F.trunks then 0 else v (⟨e,he⟩,k))
  by_cases he:e∈F.trunks
  · rw [dif_pos he,F.on_tree _ ⟨e,he⟩,one]; rfl
  let j:F.Free:=⟨e,he⟩
  rw [dif_neg he,F.off_tree _ j,local_exp_log _ (small j)]
  rfl

theorem copied_hotel_log (V:Voice G) (cle:Clear G V) (χ:ChartRatio G) (X Y:Support f)
    (O:Config G c) (μ:Positions (Key F G)) (v:F.Free→G.Color) {lo hi K r δ:ℝ}
    (paid:Couch V F μ Y χ v O lo hi K r δ) (xy:X⊆Y)
    (small:3*shade G*K < (LocalH.geom_patch G).choose) (W:Config G f) (hit:W∈hotel F X Y V O μ lo hi) (g:ℝ) :
    let U:=chambers F Y V O μ W
    chartLog g U=g⁻¹ • Rolling.stamp F G (imageNear V F U) := by
  intro U
  obtain ⟨shape,fund⟩:=anchors V F X Y O μ χ cle v paid xy W hit
  let rent:=rented F Y V O μ W
  have bound:‖rent‖≤K:=by
    rw [show rent=rent-μ+μ from (sub_add_cancel rent μ).symm]
    exact (norm_add_le ..).trans ((add_le_add (leanOn F X Y V O μ cle xy hit paid.lifts
      (paid.glued.le.trans paid.lifts)) le_rfl).trans ((add_comm ..).trans_le paid.ht))
  have outside (i:F.Free):‖tint G _ (imageNear V F U) i‖ ≤ 3*shade G*K:=by
    let a:=tint G _ (imageNear V F U) i
    let b:=tint G _ rent i
    have hb:‖b‖≤ shade G*K:=(norm_le_pi_norm (tint G _ rent) i).trans ((tint_le rent).trans (mul_le_mul_of_nonneg_left bound (shade_pos G).le))
    have h:‖a-b-v i‖≤δ:=(fund i).2
    calc
      _= ‖a-b-v i+b+v i‖:=by congr 1; dsimp only [a]; abel
      _≤(δ+shade G*K)+shade G*K := (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h hb)) (paid.sums i))
      _≤_:=by linarith only [paid.final]
  calc chartLog g U=chartLog g (Film.stretch F (imageNear V F U)):=congrArg (chartLog g) shape
       _=_:=chartLog_stretch F g _ (fun i=>(outside i).trans_lt small)

end YM.Integration.FVA1Physical.Round2.Curvature

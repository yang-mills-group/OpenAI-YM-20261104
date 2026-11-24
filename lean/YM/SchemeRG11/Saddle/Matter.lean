import YM.SchemeRG11.Saddle.Augur
/-! Normalized moment bridges. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius PowerSeries NNReal
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
open PertExtension.Series Local Radial Tested PertExtension.Chart
variable {G:Gauge}{n:Side}
def PipeF (μ: Measure (Potential G n))(O: Wilson.Config G n→ℝ):= Realm μ (Pert.Orb.action G n) priceAll (O ∘ positiveLinks)
def PipeL (μ: Measure (Land G n))(O: Wilson.Config G n→ℝ):= Realm μ (Pert.Orb.action G n ∘ g0 G n) (priceAll ∘ g0 G n) (O ∘ positiveLinks ∘ g0 G n)
def PipeT (P:ChartRatio G)(O: Wilson.Config G n→ℝ):= Realm (tangent G (Cotree n)) fiscal (jacobian P) (O ∘ representative)
lemma tree_color(P:ChartRatio G)(O: Wilson.Config G n→ℝ): PipeT P O= PowerSeries.mk (diagonalWith P (restrictedO O)):=by
 let Z:= tangent G (Cotree n)
 unfold PipeT Realm diagonalWith
 have hu : Yellow Z fiscal (jacobian P * (O ∘ representative))=PowerSeries.mk (rowsWith P (restrictedO O)):=rfl
 rw [hu,divide,show Yellow Z fiscal (jacobian P)=PowerSeries.mk (rowsWith P (n:=n) 1) by
    unfold rowsWith Yellow; congr 1; congr 1; funext x; simp [accountingWith]]
 ext n; rw [PowerSeries.coeff_mk]; rfl
lemma pipeF_color(μ:Measure (Potential G n))[μ.IsAddHaarMeasure](P:ChartRatio G)(R:LocalRatio P)(hn:Admissible n){O:Wilson.Config G n→ℝ}(h:Watching O): PipeF μ O=PipeT P O:=by
 have hp:Even n.val:= even_iff_two_dvd.mpr hn.2
 let v : Measure ↥(Flow G n):= Measure.addHaar
 let Z:= tangent G (Cotree n); let ν:= Z.prod v
 haveI : ν.IsAddHaarMeasure:= Measure.prod.instIsAddHaarMeasure _ _
 let e:=packing G hp; let c:=(P.scale ^ Fintype.card (Cotree n))⁻¹
 let K:= ∫ y,Radial.kernel costV y ∂v
 let α:= Local.alpha μ ν e
 let C:= K*(α*c)
 have hC: 0<C:= mul_pos (shade_pos v costV_light) (mul_pos (alpha_pos ..) (inv_pos.mpr (pow_pos R.scale _)))
 have hi(O:Wilson.Config G n→ℝ)(hl:Watching O):
    Yellow μ (Pert.Orb.action G n) (priceAll * (O ∘ positiveLinks)) = PowerSeries.C C * Yellow Z fiscal (jacobian P * (O ∘ representative)):=by
    let K₀(v:Potential G n):= priceAll v*O (positiveLinks v)
    let J(A:Dir G n):= jacobian P A*O (representative A)
    have hj:ContDiffAt ℝ ∞ J 0:= ((Ratio.jacobian_smooth R).of_le le_top).mul (watch_slick (hp:=hp) hl)
    have hk:ContDiffAt ℝ ∞ K₀ 0:= (priceAll_smooth.of_le le_top).mul hl.tame
    have H:∀ᶠ x:Whole G n in 𝓝 0,K₀ (graze hp x)*TraceCost hp x= c*J x.1:=by
       filter_upwards [price_snap hn (hp:=hp) P R,watch_tree (hp:=hp) hl] with x hx hv
       unfold K₀; rw [hv,mul_right_comm,hx]; change _= _ * (_ *_); ring
    have hM: Radial.moment μ K₀ (Pert.Orb.action G n)=fun i=> (α*c)*Radial.moment ν (J ∘ Prod.fst) (main G n) i:= relocation μ ν hk VF_stable VF_weight (ContDiffAt.comp (f:=fun p:Whole G n=>p.1) 0 hj contDiffAt_fst) main_station (main_goal hp) e (graze hp) (graze_smooth G hp) (graze_flat G hp) (graze_good hn) (fiscal_graphed hp) c H
    change PowerSeries.mk (Radial.moment μ K₀ (Pert.Orb.action G n))=PowerSeries.C C * PowerSeries.mk (Radial.moment Z J fiscal)
    rw [hM,show Radial.moment ν (J ∘ Prod.fst) (main G n)= fun i=> Radial.moment Z J fiscal i*K from relocation_split Z v hj fiscal_stationary costV_smooth costV_sq,← kcal]; congr 1; funext; dsimp only [C]; ring
 unfold PipeF PipeT Realm
 have hz:=hi _ watching_unit
 rw [show ((1:Wilson.Config G n→ℝ) ∘ positiveLinks)=1 from rfl,show ((1:Wilson.Config G n→ℝ) ∘ representative)=1 from rfl, mul_one,mul_one] at hz
 rw [hi O h,hz,taxa]
 · exact (yellow_pos Z (coercion hp) (by
       unfold jacobian; refine Finset.prod_pos fun i _=>?_; unfold fee; change 0<max (P.scale * P.J 0) _; rw [R.anchored,mul_one]; exact lt_max_of_lt_left R.scale)).ne'
 exact hC.ne'
lemma pipeL_color(μ:Measure (Land G n))[μ.IsAddHaarMeasure](P:ChartRatio G)(R:LocalRatio P)(hn:Admissible n){O:Wilson.Config G n→ℝ}(h:Watching O): PipeL μ O=PipeT P O:=by
 have hp: Even n.val:= even_iff_two_dvd.mpr hn.2
 obtain ⟨e,he⟩:=steeple_good (G:=G) hn (hp:=hp)
 let Z:= tangent G (Cotree n)
 let c:=(P.scale ^ Fintype.card (Cotree n))⁻¹; let C:=Local.alpha μ Z e*c
 have hc:0<C:=mul_pos (alpha_pos ..) (inv_pos.mpr (pow_pos R.scale _))
 let S:=Pert.Orb.action G n ∘ g0 G n; let U:=priceAll ∘ g0 G n
 have hi(O:Wilson.Config G n→ℝ)(h:Watching O): Yellow μ S (U*(O ∘ positiveLinks ∘ g0 G n))=PowerSeries.C C * Yellow Z fiscal (jacobian P*(O ∘ representative)):=by
    let K₀(v:Land G n):= priceAll v.val * O (positiveLinks v.val); let J(A:Dir G n):=jacobian P A*O (representative A)
    have hJ:ContDiffAt ℝ ∞ J 0:= ((Ratio.jacobian_smooth R).of_le le_top).mul (watch_slick (hp:=hp) h)
    have hk:ContDiffAt ℝ ∞ K₀ 0:=by
       have hu:ContDiffAt ℝ ∞ (fun a:Potential G n=>priceAll a*O (positiveLinks a)) (g0 G n 0):=by rw [map_zero];exact (priceAll_smooth.of_le le_top).mul h.tame
       exact ContDiffAt.comp (f:=g0 G n) 0 hu (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Land G n) (F:=Potential G n) (g0 G n)).contDiffAt
    have hg:∀ᶠ A:Dir G n in 𝓝 0,K₀ (steeple hp A)*cost (e.symm.toContinuousLinearMap ∘L fderiv ℝ (steeple (G:=G) hp) A)= c*J A:=by
       filter_upwards [price_land hn e he P R,watch_land (hp:=hp) h] with A ha hv
       unfold K₀; rw [hv,mul_right_comm,ha]; change _=_ * (_*_); ring
    have hm: Radial.moment μ K₀ S= fun i=> C * Radial.moment Z J fiscal i:= relocation μ Z hk VL_stable VL_weight hJ fiscal_stationary (coercion hp) e _ (steeple_smooth hp) (steeple_flat hp) (steeple_good hn) (fiscal_sliced hp) c hg
    change PowerSeries.mk (Radial.moment μ K₀ S)=PowerSeries.C C* PowerSeries.mk (Radial.moment Z J fiscal)
    rw [hm,kcal]
 unfold PipeL PipeT Realm
 have hz:=hi _ watching_unit
 rw [show ((1:Wilson.Config G n→ℝ) ∘ positiveLinks ∘ g0 G n)=1 from rfl,show ((1:Wilson.Config G n→ℝ) ∘ representative)=1 from rfl, mul_one,mul_one] at hz
 change Yellow μ S _ * (Yellow μ S U)⁻¹= _
 rw [hi O h,hz,taxa]
 · exact (yellow_pos Z (coercion hp) (by
      unfold jacobian; refine Finset.prod_pos fun i _=>?_; unfold fee; change 0<max (P.scale * P.J 0) _; rw [R.anchored,mul_one]; exact lt_max_of_lt_left R.scale)).ne'
 exact hc.ne'
end YM.SchemeRG11.Sway

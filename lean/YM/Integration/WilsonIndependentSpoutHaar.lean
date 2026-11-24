import YM.Integration.WilsonIndependentSpoutWilsonAction

/-! The elected finite inversion chart uses the same normalized local Haar
density in its tagged spring and its Wilson coefficient calculation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHaar
open Set Filter Lattice WilsonCoeffUV PertExtension PertExtension.Chart
open PertExtension.Orb RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Binding RegulatorIR.Prim RegulatorIR.Laplace
open WilsonIndependentSpoutWilsonAction
open scoped Classical Topology BigOperators
variable {G:Gauge}{f:Side}

theorem selected : tray G = XSpace.Bare.chart G := rfl

theorem link :
    entry G =ᶠ[𝓝 0] fun u=>Real.log ((XSpace.Bare.chart G).J u) := by
  let Q:=XSpace.Bare.chart G
  have q:=XSpace.Bare.chart_ratio G
  filter_upwards [genuine G,Metric.ball_mem_nhds (0:G.Color) q.patch] with u hu home
  rw [hu,ent,selected,fee,fee,q.anchored,mul_one,
    max_eq_left q.scale.le,max_eq_left (mul_nonneg q.scale.le (q.pos u home).le)]
  congr 1
  field_simp [q.scale.ne']

theorem read (x:Horizon G f)(i:Edge (Site f)):
    dij (XSpace.Bare.chart G) (dyes (opening x) i)=(XSpace.Bare.chart G).J (fire x i) := by
  unfold dij dyes opening
  rw [(coatC G).apply_symm_apply,(cloth G f).symm_apply_apply]
  have axis:Exterior.axisEquiv.symm (Exterior.coord i.2)=i.2:=Exterior.axisEquiv.symm_apply_apply i.2
  dsimp only [canvas];rw [axis]

theorem folded (he:Even f.val):
    ∀ᶠ x:Horizon G f in 𝓝 0,
      unhaar (XSpace.Bare.chart G) (opening x)=2*(∑ i:OEdge f,entry G (x i)) := by
  have ht (i:Edge (Site f)):Tendsto (fun x:Horizon G f=>fire x i) (𝓝 0) (𝓝 0):=by
    simp only [fire]
    split
    · exact (continuous_apply _).tendsto _
    · have e:Tendsto (fun x:Horizon G f=>x (index i)) (𝓝 0) (𝓝 0):=(continuous_apply _).tendsto _
      simpa only [neg_zero] using e.neg
  have h (i:Edge (Site f)):= (ht i).eventually (link (G:=G))
  filter_upwards [eventually_all.mpr h] with x hx
  unfold unhaar
  simp_rw [read,←hx]
  rw [←Equiv.sum_comp (Quadratic.both he) (fun i:Edge (Site f)=>entry G (fire x i)),
    Fintype.sum_sum_type]
  change (∑ i:OEdge f,entry G (fire x i.val))+(∑ i:OEdge f,entry G (fire x (reflect i.val)))=_
  simp_rw [fire_swaps x he,ent_even,fire_at,two_mul]

end YM.Integration.WilsonIndependentSpoutHaar

import YM.OPE.Compatible.Arch.Lab
/-!
# Calculator rules used in position charts
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
namespace Reads
variable {f h : ℝ→ E}{k q:JetS E}
lemma limit (ht:Reads f k): Tendsto f Lf (𝓝 k.s):=by
     have he:Tendsto (f-k.atK) Lf (𝓝 0):=ht.trans_tendsto (by convert! (show Tendsto id Lf (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).pow 3 using 1; simp)
     have hi:Continuous k.atK:=by unfold JetS.atK;fun_prop
     have hv:Tendsto k.atK Lf (𝓝 (k.atK 0)):= hi.continuousAt.continuousWithinAt
     convert he.add hv using 1
     · funext x; simp
     simp [JetS.atK]
lemma bounded (ht:Reads f k): f=O[Lf](fun _=> (1:ℝ)) := (limit ht).isBigO_one _
lemma selves (k:JetS E): Reads k.atK k:= by simp only [Reads,sub_self]; exact isBigO_zero ..
lemma cong (ht:Reads h k)(he : f =ᶠ[Lf] h): Reads f k:= ht.congr' (he.symm.sub Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl
lemma constants (k:E): Reads (fun _=>k) ⟨k,0,0⟩:= (selves _).cong (by filter_upwards with x; simp [JetS.atK])
lemma stride (k:E): Reads (fun t:ℝ=> t • k) ⟨0,k,0⟩ := (selves _).cong (by filter_upwards with x; simp [JetS.atK])
lemma ride (k:E):Reads (fun t:ℝ=> (t^2) • k) ⟨0,0,k⟩ := (selves _).cong (by filter_upwards with x; simp [JetS.atK])
protected lemma sum (a:Reads f k)(b:Reads h q): Reads (f+h) (k+q):=by unfold Reads; rw [JetS.rates_add,show f+h-(k.atK+_)=f-k.atK+(h-q.atK) by abel]; exact IsBigO.add a b
protected lemma neg (a:Reads f k): Reads (-f) (-k):=by unfold Reads; rw [JetS.rates_neg,show -f- -k.atK= -(f-k.atK) by abel]; exact IsBigO.neg_left a
protected lemma smul (c:ℝ)(a:Reads f k): Reads (c • f) (c • k):=by unfold Reads; rw [JetS.rates_scale, ←smul_sub]; exact a.const_smul_left c
lemma minus (a:Reads f k)(b:Reads h q): Reads (f-h) (k-q):=by rw [sub_eq_add_neg]; exact a.sum b.neg
variable {u v:ℝ→ℝ}{p b:JetS ℝ}
lemma pile (a:Reads u p)(c:Reads v b): Reads (u*v) (p*b):=by
     have hX: ((u-p.atK)*v) =O[Lf](gradeP 3):= by convert! IsBigO.mul a c.bounded using 2; simp
     have hY: (p.atK*(v-b.atK)) =O[Lf](gradeP 3):= by convert! IsBigO.mul ((selves p).bounded) c using 2; simp
     let d : ℝ→ℝ:=fun t:ℝ=> (p.l*b.h+p.h*b.l+t*p.h*b.h)
     have hb:p.atK*b.atK-(p*b).atK=d*gradeP 3:=by funext i; simp only [JetS.atK,gradeP,Pi.sub_apply,Pi.mul_apply,d,smul_eq_mul]; change _-(p.s*b.s+i*(p.s*b.l+p.l*b.s)+i^2*(p.s*b.h+_+_))= _;ring
     have hz : d=O[Lf](fun _=> (1:ℝ)) := (show Tendsto d Lf (𝓝 (d 0)) from (show Continuous d by unfold d; fun_prop).continuousAt.continuousWithinAt).isBigO_one _
     have hZ : (p.atK*b.atK-(p*b).atK)=O[Lf](gradeP 3):=by rw [hb]; convert! hz.mul (isBigO_refl (gradeP 3) Lf) using 2; simp
     unfold Reads; rw [show u*v-(p*b).atK= (u-p.atK)*v + p.atK*(v-b.atK)+(p.atK*b.atK-(p*b).atK) by ring]; exact (hX.add hY).add hZ
-- edits in charts. formal Pol
lemma invert (a:Reads u p)(h:p.s≠0) : Reads u⁻¹ ⟨(p.s)⁻¹, -p.l/p.s^2, p.l^2/p.s^3-p.h/p.s^2⟩:=by
     let k:JetS ℝ:=⟨(p.s)⁻¹, -p.l/p.s^2, p.l^2/p.s^3-p.h/p.s^2⟩
     have ht:= a.pile (selves k)
     have he: p*k=1:=by
        apply JetS.eta
        · change p.s*p.s⁻¹=1; rw [mul_inv_cancel₀ h]
        · change p.s*(-p.l/p.s^2)+_=0; change p.s*(-p.l/p.s^2)+p.l*p.s⁻¹=0; field_simp;ring
        change p.s*(p.l^2/p.s^3-p.h/p.s^2) + p.l*(-p.l/p.s^2)+p.h*p.s⁻¹=0; field_simp;ring
     rw [he] at ht
     have hy :(1-u*k.atK)=O[Lf](gradeP 3):=by rw [show 1-u*k.atK= -(u*k.atK-(1:JetS ℝ).atK) by rw [show (1:JetS ℝ).atK=1 by funext i; change 1+i • (0:ℝ)+ _ • (0:ℝ)=1; rw [smul_zero,smul_zero]; ring];ring]; exact ht.neg_left
     have hf : (u⁻¹-k.atK)=O[Lf](gradeP 3):=by
          have hi:(u⁻¹*(1-u*k.atK))=O[Lf](gradeP 3):=by convert! ((a.limit.inv₀ h).isBigO_one ℝ).mul hy using 2; simp
          apply hi.congr' _ Filter.EventuallyEq.rfl; filter_upwards [a.limit.eventually (isOpen_compl_singleton.mem_nhds (show _ from h))] with x (hx : u x≠0); simp [hx,mul_sub]
     exact hf
end Reads
end YM.OPE.Libra

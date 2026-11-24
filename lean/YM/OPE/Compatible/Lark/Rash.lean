import YM.OPE.Compatible.Lark.Brute
/-!
# All trace accounts, ordinary torque identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
lemma frost (p:Q!)(t:Kv)(ht:t≠0): c.val /2≤ 2+ separation (HingeT S he G (Varp S he H G t p)) (HingeT S he G p):=by
     let x:=p.1.val; let y:=S.ratio.parent x.1; have hp: separation (decks t x.1) (ferry t x).1 ≤ 1:=by
        unfold ferry Step.used; split; next he=>simp only [separation,sub_sub_cancel]; rw [←wrap_step]; refine (within_size (step _) _).trans ?_; unfold size; simp [apply_ite (f:=Int.natAbs)]
        next h=>simp
     have hP: separation (decks t y) (HingeT S he G (Varp S he H G t p)) ≤ 2:=by
        unfold y; rw [← (step_parent S.ratio H he t x.1).1]; exact (Work.E04.parent_separation S.ratio ..).trans (Nat.add_le_add_right hp _)
     exact (deck_free t ht y).trans ((separation_triangle _ _ _).trans (Nat.add_le_add_right hP _))
lemma cards : (Fintype.card Q!:ℝ)=(c.val:ℝ)^4* (Fintype.card (Slip G S.ratio.count):ℝ):=by rw [Fintype.card_congr (squad S.ratio he G), Fintype.card_prod,Lattice.site_card]; push_cast; rfl
lemma leanChart (p:Q!)(t:Kv)(M:Matrix Q! Q! ℝ): ‖(leanI S he H G t * M) p p‖= ‖M (Varp S he H G t p) p‖:=by
     let f (j:Q!):= M j p; rw [show (_*_ : Matrix Q! Q! ℝ) p p=(leanI S he H G t*ᵥ f) p from Matrix.mul_apply .., leanK]; split
     next h=>simp [f]
     next h=>rfl
lemma saluteTrace (k:ℕ)(A:Matrix Q! Q! ℝ)(D:ℝ)(h:ZoneP S he k A D): (c.val:ℝ)^k * ‖(skipH S he H G*A).trace‖ ≤ 4*Fintype.card Q! * 8^k * D:=by
     let P:= leanI S he H G; let W:ℝ:= c.val; have hw:0<W:= Nat.cast_pos.mpr c.pos
     have hp(i:Q!)(t:Kv)(ht:t≠0): W^k * ‖(P t*A) i i‖ ≤ (8:ℝ)^k*D:=by
           let y:= Varp S he H G t i; let z:= HingeT S he G; have hh : W^k ≤ (8:ℝ)^k * Dux k (z y) (z i):=by
              unfold Dux; rw [← mul_pow]; apply pow_le_pow_left₀ hw.le; have hy:c.val ≤ 8*(1+separation (z y) (z i)):=by
                   have h : c.val /2≤ 2+ separation (z y) (z i):=frost S he H i t ht
                   omega
              unfold W; exact_mod_cast hy
           rw [leanChart]; exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h.2 y i) (by positivity))
     let V:= (Finset.univ:Finset Kv).erase 0; have ht(t)(hi:t∈V): W^k * ‖(P t*A).trace‖ ≤ Fintype.card Q! * ((8:ℝ)^k*D):=by
           unfold Matrix.trace; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hw.le _)).trans; rw [Finset.mul_sum]; apply (Finset.sum_le_sum (fun i _=> hp i t (Finset.ne_of_mem_erase hi))).trans_eq; rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
     have hW: skipH S he H G= ∑ i∈V, P i:=by
           unfold skipH SUMp; rw [← Finset.sum_erase_add (a:=0) .., lean0,add_sub_cancel_right]
           exact Finset.mem_univ _
     change W^k* _ ≤ _; rw [hW, Finset.sum_mul,Matrix.trace_sum]; apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (pow_nonneg hw.le _)).trans; rw [Finset.mul_sum]; apply (Finset.sum_le_sum (fun i hi=> ht i hi)).trans; rw [Finset.sum_const,nsmul_eq_mul]; have hV:(V.card:ℝ)≤4:=by
           exact_mod_cast Finset.card_le_card (Finset.erase_subset ..)|>.trans_eq (Finset.card_univ.trans kvCard)
     apply (mul_le_mul_of_nonneg_right hV ?_).trans_eq; swap; · have hx := h.1; positivity
     ring
end YM.OPE.Cascade.Rill

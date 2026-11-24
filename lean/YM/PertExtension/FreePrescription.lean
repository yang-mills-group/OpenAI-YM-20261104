import YM.PertExtension.MeshIntegral
import YM.PertExtension.WilsonPrice

/-! Order-zero identification after the two Wick normalizations, now FINITE
X-space tests on joint UV coefficient input before position recanonicalization.
Engineering compensation per own horizon. No time reflection convention is
applied to these curvature labels; this is the ordinary polynomial moment. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.LatticePT
open Function Filter Set Wilson Lattice RG MeasureTheory Orb Gauge MvPolynomial Finset Next.Rank Next.Rank.Normal Maxwell
open Source Labels Slope Mixed Leading Node Screens Configuration
open scoped ContDiff Topology BigOperators
variable {G: Gauge}{n:ℕ}(v : Fin n→LatticePT.Word G)(q : ℕ+)(hq:1<q.val)

abbrev electrical (q : LatticePT.Word G) := Maxwell.observable G q.d (q.F.basis q.axis)
abbrev electricity (x:Points n):= Maxwell.Wick.moment G x (electrical ∘ v)
section Path
variable (w : (t:ℕ)→Native q t)(hw:∀ t,w t∈origins q t)
variable (s: (t:ℕ)→Grid.offsets q n t){x:Points n}(hx:x∈conf n)(hs:Tendsto (fun m=> Grid.sample q m (s m)) atTop (𝓝 x))
abbrev finiteQ (m:ℕ)(z:Grid.offsets q n m) := Price.ticket v q m (Price.orig q m (w m)) (lift ∘ z)
include hw hx hq hs
lemma ticket_limit : Tendsto (fun m=> finiteQ v q w m (s m)) atTop (𝓝 (electricity v x).re) := by
   classical
   let O (t:ℕ):=Price.orig q t (w t)
   let U (i:Fin n)(t:ℕ):=Lattice.lift (s t i)
   have hO:Placement q O:= placement q w hw
   have hU (i:Fin n): Tendsto _ atTop _:= Grid.sample_each hq hs i
   let D := Finset.sup (Finset.univ : Finset (Fin n)) (fun i=>(v i).d); have hd i : (v i).d≤D := Finset.le_sup (f:=(fun i=>(v i).d)) (Finset.mem_univ i)
   let u0:= fun i=>thawKey (raiseLabel G (hd i) ((v i).F.basis (v i).axis))
   have ht := Leading.top_limit (s:=(Finset.univ : Finset (Fin n))) q hq hO hx hU v hd
   dsimp only at ht;have hh:=Complex.continuous_re.continuousAt.tendsto.comp ht
   change Tendsto _ _ (𝓝 ((blend (currentX hx G D) 0 (pot Finset.univ u0)).re)) at hh
   rw [← G_moment hx ] at hh
   refine hh.congr (fun t=>?_)
   have hK : Leading.KK (G:=G) q O U t=Price.KK q t (routes O U t):=by
       ext1; funext a b
       have he:=Node.joint_matches (G:=G) (n:=side q t) (routes O U t)
       unfold Price.KK; rw [show (wrap _ ∘ routes O U t)=(fun i=>wrap _ (routes O U t i)) from rfl,he];rfl
   dsimp only [Function.comp_apply] at *
   rw [hK, ← Complex.ofReal_pow, Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
   rfl

end Path
end YM.PertExtension.LatticePT

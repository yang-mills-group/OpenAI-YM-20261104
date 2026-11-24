import YM.OPE.Compatible.Pendulum.Ore
/-! Uniform costs across choices of K and initial/F frames. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F K:Finset X}{m j s':X→ℕ}{l:ℕ→ℕ}
   {G:Gauge}{C:Family G}{L:Extraction.Order}{A:Allot C} {W d e k n J b s t:ℕ}
   {Q:brim D U→ℝ}
-- sum tensor. substitute all combs *not* containing pivot once. all paths and tax counts.
def purse (C:Family G)(v:X)(m j:X→ℕ)(F:Finset X)(d k H:ℕ) (r a c:ℝ)(U:brim D F→ℝ):= a^(F.card*(places X+places X))*Run.Below C.path ((lantern C.path r d k (j v))/2) (j v) (finishAt D m v)*((event_fee H c)^(Fintype.card X)*(event_fee H c)^(Fintype.card X))*∏ i ∈ univ\ cove D F v,U i
-- note purse multiplied a factor with real div. need compare F≤U
lemma exchange_fee (S:Wave m U K (k+1))(S':Wave m K F k)(x:brim D F)(hp:x.val∈brim D K){c a r:ℝ}{H:ℕ}(hc:0<c)(hg:c≤1)(ha:0<a)(he:a≤1)(hx:0<r)(hQ:∀ i,0 ≤ Q i) :
    purse D C x.val m j U d k H r a c Q ≤ a^(F.card*(places X+places X))* (Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val)*(∏ i∈univ.erase x,feedS D S' (feedS D S Q H c) H c i)):=by
   let u':= event_fee H c; let q:= Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val); let y:= (⟨x.val,hp⟩:brim D K); let X':= places X+places X; let au:=a^(U.card*X'); let s:=univ\cove D U x.val; let b₀:=∏ i∈ s,Q i; let V(K':Finset X)(p':brim D K'):=univ.erase p'
   have ht:0 ≤ u':= pow_nonneg hc.le _; have hh: u'≤1:=pow_le_one₀ hc.le hg
   have hr': 0 ≤ q:= (Run.below_fee _ (div_pos (lan_pos C.path hx) zero_lt_two)).le; have hU:0 ≤ b₀:= Finset.prod_nonneg (fun _ _=>hQ _)
   have hζ(K':Finset X)(p':brim D K'): u'^(Fintype.card X) ≤ u'^ (V K' p').card:= pow_le_pow_of_le_one ht hh (((card_erase_le (s:=univ) (a:=p'))).trans (by rw [card_univ,Fintype.card_coe];exact card_le_univ _))
   have hv:(∏ i∈univ.erase x,feedS D S' (feedS D S Q H c) H c i)=u'^(V F x).card*(u'^(V K y).card*b₀):=by
       rw [show (∏ i∈univ.erase x,feedS D S' (feedS D S Q H c) H c i)= _ from prod_mul_distrib, prod_const, besides_cove]; rw [← elements_bunch D S',singleton_later D S' x y rfl,sdiff_singleton_eq_erase]; rw [show (∏ i∈univ.erase y,feedS D S Q H c i)= _ from prod_mul_distrib,prod_const,besides_cove D S]
   change au*q*_*b₀≤_; rw [hv]
   let g (p:ℕ):= u'^(p:ℕ)
   have ht' :g (Fintype.card X)*g (Fintype.card X) ≤ g (V F x).card*g (V K y).card:=mul_le_mul (hζ F x) (hζ K y) (pow_nonneg ht _) (pow_nonneg ht _)
   simp_rw [← mul_assoc]
   exact mul_le_mul_of_nonneg_right ((show au*q*g (Fintype.card X)*g (Fintype.card X)=au*q*(g (Fintype.card X)*g (Fintype.card X)) from by rw [mul_assoc _ _ (g _)]).le.trans ((mul_le_mul ((mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ha.le he (Nat.mul_le_mul_right X' (card_le_card (S'.next.trans S.next)))) hr')) ht' (mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _)) (mul_nonneg (pow_nonneg ha.le _) hr')).trans_eq (mul_assoc _ _ _|>.symm))) hU
end YM.OPE.Arboreal.Pixel

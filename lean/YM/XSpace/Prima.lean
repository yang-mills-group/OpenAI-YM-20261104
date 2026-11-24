import YM.XSpace.Arenas

/-! # Book convergence on positive-radius scales -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Drama
open Lattice Scale Sail Litter Trace Tide Future Mu Further.FreeCovariance.KP Function Set Filter Chart2 MvPolynomial Lows
open scoped Topology BigOperators ContDiff
variable {ι:Type}{L:Filter ι}{F:Type*} {G:Gauge}{k d n m:ℕ}
variable {X:ι→Contact G} {A:ι→ℝ}{r:ι→Cover}
def tick (A:ι→ℝ)(i:ι)(k:ℕ):ℂ:=(A i:ℂ)⁻¹^k
def Sees (L: Filter ι)(A:ι→ℝ) (x:ι→Cover)(v:ι→ Contact G): Prop:= ∀ p:Fee G,Likely L fun i=> tick A i p.cost * pit (v i) (harp (displace (x i) p.line))
lemma observes (x:ι→Cover)(f:Radio G.Color)(u:E4)(h:∀ j,ContDiffAt ℝ ∞ (f j) u)(hx:∀ l j v,Tendsto (fun i=> (A i)⁻¹^(1+l.length) • crack l (Scale.twig j (X i)) (x i+v)) L (𝓝 (ride l (f j) u))): Sees L A x X:=by
  intro p; have he (l:ℕ)(i:ι)(v:ℝ):tick A i l*(v:ℂ)= ↑((A i)⁻¹^l*v):=by unfold tick; push_cast; rfl
  simp_rw [leg_test,he]; exact ⟨_,Complex.continuous_ofReal.continuousAt.tendsto.comp (prunes (X:=f) (u:=u) h p.due (x:=x) (fun i=>(A i)⁻¹^(1+p.k)) (fun v l j hl=> by rw [← hl]; exact hx l j v))⟩

-- Covers polynomial backgrounds on ALL finite-radius annuli
variable {u:E4}(B:Hat G d)(S:Tendsto A L (𝓝 0))(he:∀ᶠ i in L, 0<A i)(hx:Tendsto (fun i=>A i • rcast (r i)) L (𝓝 u))
include he hx S in
lemma homogeneous (m:ℕ)(A':Vase m G.Color): Sees L A r (fun i=> release ((A i)^(1+m) • A')):=by
  let f:Radio G.Color:= fun j=> motifValue (A' j); apply observes _ f u (fun j=>(Tensor.diag_smooth (A' j).val ∞).contDiffAt) -- binder diag belongs namespace
  intro l j v; have hp : Tendsto (fun i=> A i • rcast (r i+v)) L (𝓝 u):= by simp_rw [Cross.rcast_add,smul_add]; simpa using hx.add (S.smul_const (rcast v))
  have H:= tendency S he l (fun i=> r i+v) (half j) (fun _=> A' j) u _ tendsto_const_nhds hp; refine H.congr' ?_
  filter_upwards [he] with i hi; rw [map_smul,map_smul]; rw [map_smul]; simp_rw [← peaked,map_smul,Pi.smul_apply,smul_smul]; congr 1; rw [pow_add,pow_add]; simp_rw [pow_one]; field_simp
lemma applies {x y:ι→Contact G}(h:Sees L A r x)(hp:Sees L A r y): Sees L A r (x+y):=by
  intro p; specialize h p; specialize hp p; simp_rw [leg_test] at *; simp_rw [Pi.add_apply,map_add,Complex.ofReal_add,mul_add]; exact h.add hp
lemma silence :Sees L A r (fun _=>(0:Contact G)):=by intro p; simp_rw [leg_test,map_zero,Complex.ofReal_zero,mul_zero]; exact Likely.zero
lemma quieter (x:ℝ){p:ι→Contact G}(h:Sees L A r p): Sees L A r (x • p):=by
  intro j; specialize h j; simp_rw [leg_test] at *; simp_rw [Pi.smul_apply,map_smul,smul_eq_mul,Complex.ofReal_mul,mul_left_comm _ (x:ℂ)]; exact (Likely.const L (x:ℂ)).mul h
include he hx S in
lemma flare : Sees L A r (fun i=>scenic d (orchestra d (A i) B)):=by
  have hp j := homogeneous (m:=_) S he hx ((B j).val); intro p; simp_rw [scenic_break,leg_test,map_sum,map_smul,smul_eq_mul,Complex.ofReal_sum, Finset.mul_sum]; refine Likely.sum _ _ fun i _=> ?_; specialize hp i p; simp_rw [leg_test,map_smul,smul_eq_mul] at hp; exact hp
include he hx S
lemma rents (v w:Fee G)(hp:u≠0): Likely L (fun i=>tick A i (v.cost+w.cost)*(↑(handshake (displace (r i) w.line) v.line):ℂ)):=by
  have ht:= paid_pair w.due (advertised _ v.line v.due) hp hx he S
  refine ⟨_,(Complex.continuous_ofReal.continuousAt.tendsto.comp ht).congr fun i=>?_⟩; unfold comp tick; push_cast; rw [show v.cost+w.cost=2+v.k+w.k by unfold Fee.cost; omega]
lemma swings {P:Tile G}(h:Book G n P)(hp:u≠0)(hd:Sees L A r X)(hi:Sees L A (fun _=> 0) X): Likely L fun i=> tick A i n*pit (X i) (P (r i)):=by
  induction h with
  | zero n=>simp_rw [Pi.zero_apply,map_zero,mul_zero]; exact Likely.zero
  | unit=> simp [tick]; exact Likely.const ..
  | left q=> specialize hi q; simp_rw [originate] at hi; exact hi
  | right q=> exact hd q
  | rent x y=> simp only [pit,aeval_C,Algebra.algebraMap_self, RingHom.id_apply]; exact rents S he hx x y hp
  | add h p i j=> simp_rw [Pi.add_apply,map_add,mul_add]; exact i.add j
  | @mul p q aa ab h p' hi ih=> simp_rw [Pi.mul_apply,map_mul,show ∀ i, tick A i (aa+ab)=tick A i aa*tick A i ab from fun i=>pow_add ..]; exact Likely.congr (hi.mul ih) (Eventually.of_forall (fun i=>mul_mul_mul_comm ..))
  | scale h c ih=> simp_rw [Pi.smul_apply,map_smul,smul_eq_mul,mul_left_comm _ c]; exact (Likely.const L c).mul ih

-- and cap-weighted convergence of fields on the shell with positive separation.
def stageFee (d:ℕ)(A:ι→ℝ)(r:ι→Cover){P:Tile G}(p:Book G n P)(i:ι):Stage G d (n*(1+d)):=⟨tick A i n • (Lows.scale (A i) (overture d (P (r i)))),Submodule.smul_mem _ _ (capacity _ (recorder d p _))⟩
lemma facing {P:Tile G}(p:Book G n P)(h:u≠0)(d:ℕ): Still ℂ L (stageFee d A r p):=by
  apply redeem (V:=Stage G d _) (fun v=>readStage v _) no_change; intro v; change Likely L fun i=> view v (tick _ _ _ • _) -- edit
  simp_rw [map_smul, scaled,music_at, smul_eq_mul]; apply swings S he hx p h (flare v S he hx); apply flare v S he (u:=0); simp [show rcast 0=0 from by ext i; simp [rcast],tendsto_const_nhds]
theorem on_target (B:ι→Hat G d)(HB:Likely L B){P:Tile G}(h:Book G n P)(hp:u≠0)(hd:Sees L A r X)(hi:Sees L A (fun _=>0) X): Likely L fun i=> tick A i n*Remainder P X B A i (r i):=by
  unfold Remainder; simp_rw [mul_sub]; apply Likely.sub (swings S he hx h hp hd hi); have H:= facing S he hx h hp d
  let W:=((n)*(1+d))
  let V:= (fun i:ι=> (view (B i)).toLinearMap ∘ₗ trunc (coin (G:=G) (d:=d)) d ∘ₗ (Load G d W).subtype); have he:= send H V (fun c=> HB.cont (walk_cont (trunc coin d c.val)))
  refine he.congr (Eventually.of_forall fun i=>?_); change view (B i) (trunc _ _ _)= tick _ _ _* LTop _ _ _; unfold trunc LTop trunc; -- simplify both sides
  simp only [stageFee,Submodule.subtype_apply,LinearMap.sum_apply,map_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,show ∀ p:Cap G d, weightedHomogeneousComponent coin j (Lows.scale (A i) p)=_ from fun p=>scale_saves (A i) p j,map_smul,map_smul,pure_entry _ _ (weightedHomogeneousComponent_mem coin _ j)]; simp only [smul_eq_mul]
end YM.XSpace.Drama

import YM.WilsonCoeffUV.Wick.FieldPay
/-!
# optional post bill for Wick-read. Stable UV matrix and basis projection rates.
Note J lean Him geometry subjective. Width budgets actually installed.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Exterior Next.Free Tree Precision Power Embroider Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm Fountain PathCost
open Bank.Carp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {c f n:Side}{U V α:Type*} {G:Gauge} {h D i j k e n' b m N M r:ℕ}{F:Labels.Frame G h} {H:Hol G} {T:SectionData F}
variable {z ξ σ A' B:ℝ} {s t:ℝ}{E W C C':Credit}{p:h<D}
def threeP (F:Frame G h)(D:ℕ)(s:ℝ)(p:0<s) (r:ℕ) := ((paid_echo F s p r D).choose)
lemma threeClicks {P Q:ChamberTen G (Vote D) r}(q:Shelf Bank.terrain 0 s A' ξ P Q)(g:0<s)(i: Alma F): twain (threeP F D s g r *A') ξ (echoS F P i) (echoS F Q i):=by
    let H:= (paid_echo F s g r D).choose_spec.2; refine ⟨H _ _ _ q.wax,H _ _ _ q.wane,?_⟩; rw [← echo_minus F i q.wax q.wane g g,mul_assoc]; exact H _ _ _ q.toll

def wellfare (G:Gauge)(r h:ℕ)(s:ℝ):= ∑ i∈Finset.range (h+1), loft (Hooks G) r s (s/2) i

structure Weston (L:Theatre H T p e E W) (U:Credit) : Prop where
    hcap m (_:L.V.anchor≤ m): weightΩ L.V.draws.clock.kernel.penalty (L.V.draws.clock.J m) (L.V.draws.clock.adm m)≤L.V.cash U m
    hue m (q:L.V.anchor≤m) r:r≤h → let s:=(L.angle m q).lamp.exitS; wellfare G r h s ≤ L.V.cash U m
    honey m (q:L.V.anchor≤ m) r: r≤ h → threeP F D ((L.angle m q).lamp.exitS/2) (half_pos (L.angle m q).lamp.positive) r ≤ L.V.cash U m

theorem tinged (H:Hol G)(T:SectionData F)(p:h<D)(E W C:Credit)(e:ℕ):∃ D:Credit,∀ L:Theatre H T p e E W,Weston L C→∀ m b N M,L.V.anchor≤m→ m≤ b → b ≤ N→b ≤ M → ∀ i j, let U n:= Wray L.V.draws L.V.paid T p n m; twain (L.V.cash D m) (L.V.tempC m b) (U N i j) (U M i j):= by
   obtain ⟨U,T'⟩:=allPlays H T p e E W
   let Z:=C.prodC ((dome E).powC 2)
   let D':=(C.prodC (Z.powC h)).prodC U
   refine ⟨C.prodC D',?_⟩; intro L X m b N M w y f f' i j Q
   let A:=L.V.draws; let K n:= sea A n m; let R n:= (L.lore n m).2; let B:=L.V.cash U m
   let u:=L.V.tempC m b; let s:=(L.angle m w).lamp.exitS
   have hb:0<s:=(L.angle m w).lamp.positive
   have hp:1≤L.V.cash Z m:= Z.purchase (L.V.depth m w)
   have ht:1≤L.V.cash D' m:=D'.purchase (L.V.depth m w)
   have hU:0≤u:=(trail_pos ..).le
   have hz:0≤ B:= zero_le_one.trans (U.purchase (L.V.depth _ w))
   let r:=valence F i; let t:= (threeP F D (s/2) (half_pos hb) r)
   obtain ⟨a,b',e'⟩:= tolling L.V C w y f f' (X.hcap m w)
   have he:= ivory (P:=R N j 0) (Q:=R M j 0) (j:=h) (r:=r) (half_lt_self hb) (half_pos hb) a b' e' hp hU (fun i _=>T' 0 (valence F j) _ (Nat.zero_le _) L m w b N M y f f' j rfl)
   have hw: wellfare G r h s ≤ L.V.cash C m:= X.hue m w _ (valence_cap ..); have hc: t≤L.V.cash C m:= X.honey m w _ (valence_cap ..)
   have hy: L.V.cash D' m = L.V.cash C m*(L.V.cash Z m)^h*B:=by unfold D' B Z; simp only [cash,Credit.products, Credit.power]
   have he:= he.step (show _≤L.V.cash D' m from by rw [hy]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw (pow_nonneg (zero_le_one.trans hp) h)) hz) hU
   have hh:= threeClicks he (half_pos hb) i
   exact hh.lift (show _ ≤ L.V.cash (C.prodC D') m from (mul_le_mul_of_nonneg_right hc (zero_le_one.trans ht)).trans_eq (Credit.products C D' _).symm) hU

-- direct stable budget for inverse, too.
structure Baas (H:Hol G)(T:SectionData F)(p:h<D)(E W C:Credit)(e:ℕ) where
    arch : Theatre H T p e E W
    budget : Weston arch C
    m : ℕ
    b : ℕ
    N : ℕ
    M : ℕ
    top : arch.V.anchor≤m
    paid : m≤ b
    leg : b≤N
    base : b≤M
variable (H T e E W C p)
theorem belt :∃ D:Credit,∀ L:Theatre H T p e E W,Weston L C→∀ m b N M,L.V.anchor≤m→m≤ b → b≤N→b≤ M→∀ i j,let U n:= (Wray L.V.draws L.V.paid T p n m)⁻¹; twain (L.V.cash D m) (L.V.tempC m b) (U N i j) (U M i j):=by
   let D:= Baas H T p E W C e; let f (v:D):=v.arch.V.y v.m; let θ (v:D):= v.arch.V.tempC v.m v.b
   let P (v:D) z:=Wray v.arch.V.draws v.arch.V.paid T p z v.m; let A v:= P v v.N; let B v:=P v v.M
   have he:Brite f θ:= ⟨fun v=>v.arch.V.depth v.m v.top,fun i=>(trail_pos ..).le⟩
   have hp (v:D) z (h:v.b≤z):leaseM 1 F (P v z):= wick_stand _ (production v.arch (v.paid.trans h) v.top).1 ..
   obtain ⟨u,hu⟩:=tinged H T p E W C e
   have hx:CreditsS f θ A B:=fun i j=>⟨u.d,u.x,zero_le_one.trans u.good,fun v=>hu v.arch v.budget v.m v.b v.N v.M v.top v.paid v.leg v.base i j⟩
   obtain ⟨K,hK⟩:=cashier he (hx.ride (L:=fun _=>1) he)
   refine ⟨K,?_⟩; intro L h m b n M k r i j v w U
   let P :D:= ⟨L,h,m,b,n,M,k,r,i,j⟩
   change twain (K.buy (f P)) _ ((A P)⁻¹ v w) ((B P)⁻¹ v w); rw [steed_value (hp P P.N P.leg),steed_value (hp P P.M P.base)]; exact hK P v w
end YM.WilsonCoeffUV.Cosmos

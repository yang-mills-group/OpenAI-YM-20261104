import YM.WilsonCoeffUV.Stable.Difference
import YM.WilsonCoeffUV.Root.UV.TVPrice
/-!
# Stable D ticket. align level revenues with post firm. Input P test uses measure order; overengineering derivative count/horizon shape. Width and Crank pre independent from beacon.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{r h D l j i e k a m b u N M:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A C t B x δ:ℝ}

structure Rails (h k u e:ℕ) : Prop where
   hk:h≤ k
   rung:h+(h+1)≤u
   high:(h+1)*(k+e)≤ u
   sup:h*h≤u
lemma Rails.read(p: Rails h k u e)(he:r≤k+e): (h+1)*r≤u:= (Nat.mul_le_mul_left (h+1) he).trans p.high
lemma rail_noun (h k e:ℕ)(p:h≤k) (r:ℕ): ∃ u:ℕ,r≤u∧Rails h k u e:=⟨r+(h+(h+1))+(h+1)*(k+e)+h*h,by omega,⟨p,by omega,by omega,by omega⟩⟩

def CottonW (H:Hol G)(T:SectionData F)(p:h<D)(v: Rails h k u e)(i r:ℕ) (z:r≤k+e):ℕ:= (sterileCost F H T p v.hk i u r v.rung (v.read z) v.sup).choose

def Daunt (H:Hol G)(T:SectionData F)(p:h<D)(v: Rails h k u e)(i r:ℕ) (z:r≤k+e) (I:Cloister G h):ℝ:= ((sterileCost F H T p v.hk i u r v.rung (v.read z) v.sup).choose_spec I).choose

def CountC (F:Frame G h)(T:SectionData F)(p:h<D)(v:Rails h k u e) (i r:ℕ):ℕ:= (cheapPorts F T p v.hk v.sup i r).choose

def Cans (F:Frame G h)(T:SectionData F)(p:h<D)(v:Rails h k u e) (i r:ℕ)(I:Gear G):ℝ:= ((cheapPorts F T p v.hk v.sup i r).choose_spec I).choose

structure CompassP (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e) (I:Cloister G h) (C:ℝ): Prop where
   preD r : r≤k+e →  permeability H F p u r I.lamp/(inkPin I).patch.L.val ≤ Real.exp (-Real.log (inkPin I).patch.L.val/2)
   ann i r: i≤e → ∀ h:r≤k+e,Daunt H T p v i r h I ≤ C
   can i r: i≤e → r≤k+e → Cans F T p v i r (inkPin I)≤ C
structure Torch (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K:Credit) where
   L : Theatre H T p e E W
   ticket m (h:L.V.anchor ≤ m): CompassP H T p v (L.angle m h) (L.V.cash K m)

lemma twig_Offer {X:ChamberTen G (Vote D) r}(w:u≤k)(p:Twig 0 s A X)(hs:0<s)(y:1≤t)(h:s⁻¹≤t): Fruit 0 1 u X (A*(billingQ (Hooks G) r k).buy t):=by
    have hx:= rootV (P:=X) p hs h k; refine Fruit.slice ((Fruit.more (P:=X) (by
      unfold Fruit Award hedge autumn; simp_rw [one_mul]; apply budget_minor hx (fun i=>mul_nonneg (by positivity) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))) (norm_nonneg _))) (mul_le_mul_of_nonneg_left (offer_expands (α:=Hooks G) (r:=k) (k:=r) y) p.1))) zero_le_one w
lemma turnKeys {Y Z:Ten (Vote D) (YForest G) r}(p:Shelf Bank.terrain 0 s A δ Y Z)(h:0<s)(v:1≤C)(w:s⁻¹≤C)(u:ℕ): YieldP 0 1 u (A*(billingQ (Hooks G) r u).buy C) δ Y Z:=⟨twig_Offer le_rfl p.wax h v w,twig_Offer le_rfl p.wane h v w,(show A*δ*_= _ from mul_right_comm A δ _) ▸ twig_Offer le_rfl p.toll h v w⟩
lemma YieldP.expand {P Q:ChamberTen G (Vote D) r}(v:YieldP 0 1 u A δ P Q)(h:δ≤s): YieldP 0 1 u A s P Q:=⟨v.wax,v.wane,v.toll.more (mul_le_mul_of_nonneg_left h v.nn)⟩

def ferris (H:Hol G)(T:SectionData F)(p:h<D)(e r u:ℕ)(E W:Credit):= ((allPlays H T p e E W).choose).prodC ((billingQ (Hooks G) r u).usingC W)
def cohortC (H:Hol G)(T:SectionData F)(p:h<D)(e r u:ℕ)(E W:Credit):= (jump E (full_vacuum G (e+1) E).choose).plus (ferris H T p e r u E W)
variable {H: Hol G}{T:SectionData F}{p:h<D} {E W K:Credit}
lemma creed (L:Theatre H T p e E W)(ha:L.V.anchor≤m)(hb:m≤b)(hn:b≤N)(hv:b≤M)(u r:ℕ)(x:Alma F)(hp:i≤ e):YieldP 0 1 u (L.V.cash (ferris H T p e r u E W) m) (L.V.tempC m b) ((L.lore N m).2 x i r) ((L.lore M m).2 x i r):= by
    let V:=L.V; let I:=L.angle m ha; let Q:=(allPlays H T p e E W).choose; have he: Sees H T p e E W Q i (valence F x) r:= (allPlays H T p e E W).choose_spec i _ r hp
    rw [cash, ferris,Credit.products,Credit.stock_up]; exact turnKeys (he L m ha b N M hb hn hv x rfl) I.lamp.positive (W.purchase (V.depth _ ha)) (L.spend m ha).cap u
-- Level receipts. Funding y global
lemma leaseS (L:Theatre H T p e E W)(ha:L.V.anchor≤m)(hb:m<b)(hn:b≤N)(hv:b≤M)(hi:i≤ e)(u r:ℕ):
    let V:=L.V; let I:=inkPin (L.angle m ha); let Q:= cohortC H T p e r u E W; ∃ R:Rally (i+1) 0 I, R.σ= V.cash (doubling E) m * V.tempC m b ∧ R.x=V.cash Q m ∧ ClaimP V.draws N m (hb.trans_le hn) V.hG V.green (V.mint m ha) I R.P ∧ ClaimP V.draws M m (hb.trans_le hv) V.hG V.green (V.mint m ha) I R.Q ∧∀ j v,v≤ i→ YieldP 0 1 u R.x R.σ ((L.lore N m).2 j v r) ((L.lore M m).2 j v r):=by
   intro V I Q; let K:=(full_vacuum G (e+1) E).choose; have hy:=V.depth _ ha
   have hu:= elderT (k:=i+1) (j0:=0) V ha hb hn hv (fun i j v=>(full_vacuum G (e+1) E).choose_spec i (by unfold lowerGrade at v; omega) j)
   let H':=V.cash (doubling E) m * V.tempC m b; have he:= V.dominates_both ha hb; have hs : V.tempC m b≤ H':=le_mul_of_one_le_left (trail_pos ..).le (Credit.purchase (doubling E) hy)
   have hH:0≤ H':= (trail_pos ..).le.trans hs
   obtain ⟨R,h,h',q,q'⟩:= garageC V.draws V.paid (V.mint m ha) _ V.hG V.green hb hn hv (Q.purchase hy) he.1 he.2 (show (V.mint m ha).runs (i+1) 0 H' (V.cash Q m) N M from fun i j r=> (hu i j r).up (Credit.thickens _ hy) hH) (L.effort m ha)
   refine ⟨R,q',q,⟨(L.effort m ha).1,h⟩,⟨(L.effort m ha).1,h'⟩,fun j v t=>?_⟩
   rw [q,q']; exact ((creed L ha hb.le hn hv u r j (t.trans hi)).expand hs).step (Credit.thickened _ hy) hH
-- consts
variable {v:Rails h k u e}
def rocket (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(i r:ℕ)(z:r≤k+e)(E W K:Credit) :Credit:= K.prodC ((cohortC H T p e r u E W).powC (CottonW H T p v i r z))
def buoy (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(i r:ℕ)(E W K:Credit) := K.prodC ((cohortC H T p e r u E W).powC (CountC F T p v i r))
lemma boat (t:Torch H T p v E W K)(ha:t.L.V.anchor≤m)(hv:m<N)(u':i≤e)(z:r≤k+e):
    let L':= t.L; let V:=L'.V
    ∀ P:TowerS G D,On k P→ opal F P=0→∀ X A:ℝ, Fruit 0 1 u (P.2 i r) X→0≤A→(∀ i' j,lowerGrade i' j i r→Fruit 0 1 u (P.2 i' j) A) →
     Fruit 0 1 u ((Sink V.draws V.paid T p N m k P).2 i r) (Real.exp (-arc V.draws.S m/2)*X + V.cash (rocket H T p v i r z E W K) m*A):=by
    intro L V P w he X A f a hp; let I:=L.angle m ha; obtain ⟨R,g,h',s,_,q⟩:= leaseS L ha hv (le_refl N) (le_refl N) u' u r
    obtain ⟨Z⟩:= (L.effort m ha).2 N hv _ _ _ s.2; let Q:=cohortC H T p e r u E W; let D':= CottonW H T p v i r z
    apply (((sterileCost F H T p v.hk i u r v.rung (v.read z) v.sup).choose_spec I).choose_spec.2 V.draws V.paid N m R hv V.hG V.green _ s P w he (production L hv.le ha).1 Z (fun i j h=>(q i j h).wax) X A f a hp).more
    have hm:(inkPin I).patch.L=V.draws.S.block m:= by rw [s.1]; rfl
    refine add_le_add (mul_le_mul_of_nonneg_right ((t.ticket m ha).preD r z |>.trans_eq (by rw [arch,show (inkPin (t.L.angle m ha)).patch.L = _ from hm])) f.C) ?_
    apply mul_le_mul_of_nonneg_right _ a; unfold rocket cash; rw [Credit.products,Credit.power]; have ht:= R.rich; change Daunt H T p v i r z I* R.x^D'≤ _; rw [h'] at ht ⊢; exact mul_le_mul_of_nonneg_right ((t.ticket m ha).ann _ _ u' z) (pow_nonneg (zero_le_one.trans ht) _)
lemma brace (t:Torch H T p v E W K)(ha:t.L.V.anchor≤m)(hv:m<b)(hn:b≤N)(hm:b≤ M)(u':i≤e)(z:r≤k+e):
    let L':= t.L; let V:=L'.V; let θ:= V.cash (doubling E) m * V.tempC m b
    ∀ X:ℝ,0≤X→∀P Q:TowerS G D,(∀ j r,j≤ i→YieldP 0 1 u X θ (P.2 j r) (Q.2 j r))→
    let A:= V.cash (buoy H T p v i r E W K) m * X; YieldP 0 1 u A θ ((Sink V.draws V.paid T p N m k P).2 i r) ((Sink V.draws V.paid T p M m k Q).2 i r)∧ ∀ i':Alma F,∀ j≤ i,twain A θ (coeff j (Spray V.draws V.paid T p N m k P i')) (coeff j (Spray V.draws V.paid T p M m k Q i')):=by
    intro L V θ X hX P Q e' B; let I:=L.angle m ha; obtain ⟨R,g,h',s,v',q⟩:= leaseS L ha hv hn hm u' u r
    obtain ⟨x,y⟩:= ((cheapPorts F T p v.hk v.sup i r).choose_spec (inkPin I)).choose_spec.2 V.draws V.paid N M m R (hv.trans_le hn) (hv.trans_le hm) V.hG V.green _ s v' X hX P Q (by rw [g]; exact e') q
    have hp:= R.rich; have he:Cans F T p v i r (inkPin I)*R.x^CountC F T p v i r*X ≤ B:= by
        rw [h'] at hp ⊢; unfold B buoy cash; rw [Credit.products,Credit.power]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((t.ticket m ha).can _ _ u' z) (pow_nonneg (zero_le_one.trans hp) _)) hX
    have hθ:θ=R.σ:=g.symm; rw [hθ]; exact ⟨x.step he R.θ,fun i j v'=> (y i j v').lift he R.θ⟩
end YM.WilsonCoeffUV.Shard

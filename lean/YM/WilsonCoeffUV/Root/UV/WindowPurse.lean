import YM.WilsonCoeffUV.Root.UV.LimitRecurrence
/-!
# Uniform costs of full matrices and limiting canonical frame. Post floor only.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V α β:Type*}{r h D l e j k a N M m b i q:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{s t t' A B C x y δ σ γ S O v:ℝ}
variable {E W U' V':Credit}{T:SectionData F}{p:h<D}{θ:ℕ→ℝ}
-- all entries all at one Post-price independent iteration.
def maxW (H:Hol G)(F:Frame G h)(p:h<D)(e:ℕ):= (armada H F e 0 p).choose
def wageR (H:Hol G)(F:Frame G h)(p:h<D)(e:ℕ)(I:Cloister G h):= ((armada H F e 0 p).choose_spec I).choose
def flagD (H:Hol G)(F:Frame G h)(p:h<D)(e:ℕ):= (summarize F 0 e D (maxW H F p e)).choose
def flagC (H:Hol G)(F:Frame G h)(p:h<D)(e:ℕ)(I:Cloister G h):= ((summarize F 0 e D (maxW H F p e)).choose_spec I.lamp (wageR H F p e I) ((armada H F e 0 p).choose_spec I).choose_spec.1).choose
lemma fullStack (I:Cloister G h)(P:Rally (e+1) 0 (inkPin I))(Y Z:Island F D)(W X:Island F D)(H:Hol G)(p:h<D)(V:Turbine I P.P Y W)(S:Turbine I P.Q Z X)(A:Courant I P.P)(C: Courant I P.Q)(i:Alma F)(t:∀ j≤ e,∀ k,Shelf Bank.terrain 0 I.lamp.input P.x P.σ (Y.2 i j k) (Z.2 i j k))(v w) (hp:v≤e):
    let M:= prismata F (legion P.P Y.2); let N:=prismata F (legion P.Q Z.2); twain (flagC H F p e I * P.x^flagD H F p e) ((1+P.x)*P.σ) (lineS M v w i) (lineS N v w i):=by
    intro M N; let Z':Tand I.lamp e 0 D:=⟨P,Y.2 i,Z.2 i,fun j k h=> t j (by unfold lowerGrade at h; omega) k⟩
    obtain ⟨u,h,g⟩:= fundsN Y Z Z' i rfl rfl V.walk S.walk; let K:= wageR H F p e I; let x:= P.x
    have hx:= t e le_rfl 0
    have hE:= ((armada H F e 0 p).choose_spec I).choose_spec.2 Z' A C (by unfold dues; simp; linarith [I.lamp.inlet]) u h g x (x*P.σ) hx.wax hx.wane hx.toll
    have he:= ((summarize F 0 e D (maxW H F p e)).choose_spec I.lamp K ((armada H F e 0 p).choose_spec I).choose_spec.1).choose_spec.2 Z' x _ _ (zero_le_one.trans P.rich) hE; have hh: v<e∨ v=e∧ 0≤ valence F w:=by omega
    unfold M N; rw [coined,coined]; refine ⟨he.pose _ _ hh,he.vale _ _ hh,?_⟩; rw [← mul_assoc]; exact he.toll _ _ hh
-- additional cost only.
structure ChorusLine (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(C D' E: Credit) where
    arch : Theatre H T p e C D'
    registrar i (v:arch.V.anchor≤ i) : flagC H F p e (arch.angle i v) ≤ arch.V.cash E i
variable {C':Credit}(L:ChorusLine H T p e E W C')
abbrev scorD (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(W E:Credit):= blockAge G e E ((allPlays H T p e E W).choose)
def robePort (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W V:Credit):Credit:= ((V.prodC ((scorD H T p e W E).powC (flagD H F p e))).prodC (Credit.unit.plus (scorD H T p e W E))).prodC (doubling E)
lemma opening (u:L.arch.V.anchor≤m)(v:m<b)(h0:b≤N)(pM:b≤M)(a t: Alma F)(hk:k≤e):
    let V:=L.arch.V; twain (V.cash (robePort H T p e E W C') m) (V.tempC m b) (lineS (Jacob V.draws V.paid T p N m) k a t) (lineS (Jacob V.draws V.paid T p M m) k a t):=by
    intro V; let l:=valence F t; let I:= L.arch.angle m u; let i:= L.arch; let δ:= V.ωJ m b
    let A:=(allPlays H T p e E W).choose; let B:=(full_vacuum G (e+1) E).choose; let y:= V.y m; let D:=doubling E
    have hp j d r (h': j≤ e): Sees H T p e E W A j d r:= (allPlays H T p e E W).choose_spec j d r h'
    obtain ⟨r,u',t'⟩:= buoyant (k:=0) (i:=e) (l:=l) i u le_rfl v h0 pM (fun j d r p=>hp j d r (by unfold oldJobs at p; omega)); have hv:= V.dominates_both u v; let f:= scorD H T p e W E; let x:= f.buy y; have hh: 1≤ y:= V.depth m u; have hy:1≤ x:= f.purchase hh
    obtain ⟨W',aN,aM,he,hf⟩:= garageC V.draws V.paid _ I V.hG V.green v h0 pM hy hv.1 hv.2 r (L.arch.effort m u)
    obtain ⟨G'⟩:= (L.arch.effort m u).2 _ _ _ _ _ aN; obtain ⟨H'⟩:= (L.arch.effort m u).2 _ _ _ _ _ aM
    let Y:=L.arch.lore N (m+1); let Y':=L.arch.lore M (m+1)
    have hU (j)(p:j≤e)(r): Shelf Bank.terrain 0 I.lamp.input W'.x W'.σ (Y.2 t j r) (Y'.2 t j r):=by
        rw [he,hf]; have hg:= L.arch.touch m u; let θ:= V.tempC (m+1) b
        have hq := (hp j l r p L.arch (m+1) (by omega) b N M v h0 pM t rfl).shrink hg
        have hz: V.cash A (m+1)≤ x:= le_trans (V.shift_z A u) (le_trans (Credit.thickened (jump E B) hh) (Credit.thickens _ hh))
        exact Shelf.step ⟨hq.wax,hq.wane,hq.toll.cost (mul_le_mul_of_nonneg_left (V.also_temp u) (zero_le_one.trans (A.purchase (L.arch.V.depth _ (by omega)))))⟩ hz (le_trans (Real.sqrt_nonneg _) hv.1)
    have hw:= fullStack I W' Y Y' _ _ H p (shaft i u (by omega) W'.P aN G') (shaft i u (by omega) W'.Q aM H') G' H' _ hU _ a hk
    have hT: legion W'.P Y.2 = i.goneC N m:= Eq.symm (byPath V.draws V.paid (v.trans_le h0) V.hG V.green _ _ _ (i.effort m u).1 _ aN)
    have hS: legion W'.Q Y'.2=i.goneC M m:= Eq.symm (byPath V.draws V.paid (v.trans_le pM) V.hG V.green _ _ _ (i.effort m u).1 _ aM)
    dsimp only at hw; rw [hT,hS,he,hf] at hw
    let d:= flagD H F p e; let z:= C'.buy y*x^d; let X:=(Credit.unit.plus f).buy y; have hF:D.buy y≥1:=D.purchase hh; have hhp:1+x≤ X:=by simpa only [Credit.unit_cost] using Credit.fuel Credit.unit f hh
    have hZ:0 ≤ z:= mul_nonneg (zero_le_one.trans (C'.purchase hh)) (pow_nonneg (zero_le_one.trans hy) d)
    rw [cash,robePort,Credit.products,Credit.products,Credit.products,Credit.power]; have hs : flagC H F p e I*x^d≤ z:= mul_le_mul_of_nonneg_right (L.registrar m u) (pow_nonneg (zero_le_one.trans hy) d); have hA:z≤ z*X*(D.buy y):=(le_mul_of_one_le_right hZ (by linarith)).trans (le_mul_of_one_le_right (mul_nonneg hZ (by linarith)) hF)
    refine ⟨hw.main.trans (hs.trans hA),hw.side.trans (hs.trans hA),hw.gap.trans ?_⟩
    let g:= V.tempC m b; have hv:0≤ g:= (trail_pos ..).le; change _*((1+x)*(D.buy y*g)) ≤ z*X*D.buy y*g; rw [← mul_assoc,← mul_assoc _ _ g]; apply mul_le_mul_of_nonneg_right _ hv; exact mul_le_mul_of_nonneg_right (mul_le_mul hs hhp (by positivity) hZ) (zero_le_one.trans hF)
end YM.WilsonCoeffUV.Cosmos

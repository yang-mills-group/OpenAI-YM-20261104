import YM.SignedWilsonExpansion.Belle.Lark
import YM.SignedWilsonExpansion.Belle.Veto
/-! # Regular cleanup of horizon after deterministic root education. 'M<T length?` consume. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.SignedWilsonExpansion.Belle
open FVA2 FVA2.Scale FVA2.Dframe Dancer Dancer.Drawing Dancer.SeatsW
open Dancer.Shell Dancer.Fort Lark
open Asymptotics Filter Function Set XSpace XSpace.Structure1 Normalize Gauge
open MS MS.Local.Physical MS.High MS.Land MS.Native MS.Fleet Maxwell Maxwell.Free Maxwell.Wick
open Commission.Gram Path WilsonCoeffUV.Mer.Xa.MarqueQ.Crops Future Lesson Buffet
open scoped Topology BigOperators Classical
variable {G:Gauge}{ι κ:Type} {L:Filter ι}{θ ψ τ ε:ι→ℝ} {d l m t e a b n:ℕ}
namespace Wipe
variable (W:Initialize G){V: Normalize.Store G}(K: Rose.Pick V){Y:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {S:Prescription (Press.portDeck G)}(M:Speed.Quoted W K Y S)(s:G.Simple)
local notation "D"=> FVA2.Scale.Measure.start W K d
lemma stop (x: Tendsto τ L (𝓝 0)): τ=O[L] (1:ι→ℝ):= isBigO_const_of_tendsto x one_ne_zero
lemma powerT (h:Tendsto θ L (𝓝 0))(hθ:IsEquivalent L θ τ)(ht:l≤a): ( θ ^ a )=O[L] (τ^l):=by
    refine IsBigO.trans_isEquivalent ( IsBigO.of_bound' (?_) ) ( hθ.pow l ); filter_upwards [( h.norm.eventually_le_const (by simp: ‖(0:ℝ)‖<1) )] with i hi; simp only [Pi.pow_apply,norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hi ht
-- ↑cast issue.Fix
lemma expense (h:Tendsto θ L (𝓝 0)) (hθ:IsEquivalent L θ τ)(ht:m<a): ( θ ^ a )=o[L](τ^m):=by
     obtain ⟨b,rfl⟩:= Nat.exists_eq_add_of_le (show 1≤a from Nat.zero_lt_of_lt ht); -- gives a =??? add
     rw [add_comm 1 b,pow_succ]; exact ((powerT h hθ (Nat.le_of_lt_succ (by omega):m≤b)).mul_isLittleO (( isLittleO_one_iff ℝ ).mpr h)).congr_right (fun i=> by change (_*(1:ℝ))=_; rw [mul_one])
-- Orbit repricer in comparing t & actual.Track.D.Kind
lemma swing (q e':ι→ℂ)(h:q=O[L](1:ι→ℝ))(v:e'=O[L](1:ι→ℝ))(s:(q-e')=o[L] ε)(i:ℕ): (q^i-e'^i)=o[L] ε:=by
    induction i with
    | zero=> simp; exact isLittleO_zero ..
    | succ i ih=> rw [pow_succ,pow_succ]; exact Buffet.muCash (x:=q^i) (x':=e'^i) (y:=q) (y':=e') h ( ( v.pow i ).congr_right fun i=> one_pow _ ) s ih
lemma guise {p:ι→ℝ}(h:θ=o[L] p): (fun i=> (θ i:ℂ))=o[L] p:= (IsLittleO.of_norm_left (by simpa using h.norm_left))
lemma earth_p (h:τ=O[L] θ): (fun i=>(τ i:ℂ))=O[L] θ:= IsBigO.of_norm_left ( by simpa using h.norm_left )
variable {x:ι→View G d} {U:Set (Points n)}
include M s
lemma orbit_price (v:Roi U)(p:θ=O[L](1:ι→ℝ))(q:τ=O[L](1:ι→ℝ))(h:(θ-τ)=o[L] ε)(T:Tags G d n)(e:ℕ): Serves L (fun i y=> mote D e y (θ i) T) (fun i y=>mote D e y (τ i) T) U ε:=by
     let E:= diners L U; refine banquet.mpr (?_); change (fun i :ι×Points n=> mote D _ _ _ T-mote D _ _ _ T)=o[E]( ε∘Prod.fst ); unfold Path.mote; simp_rw [← Finset.sum_sub_distrib, ←sub_mul]; apply IsLittleO.sum; intro i hi
     have hp: (fun j=> (θ j:ℂ)-(τ j:ℂ))=o[L] ε:= ( guise h ).congr_left fun i=> Complex.ofReal_sub ..; exact ((( swing _ _ (earth_p p) (earth_p q) hp i ).comp_tendsto plot_le).mul_isBigO ( Path.cost (L:=L) W K M s v i T ) ).congr_right (fun i=> mul_one _)
lemma lessen (v:Roi U)(p:Tendsto θ L (𝓝 0))(T:Tags G d n)(h:IsEquivalent L θ τ)(hp:e≤b): Serves L (fun i y=> mote D b y ( θ i ) T) (fun i y=> mote D e y (θ i) T) U (τ^e) :=by
     induction hp with
     | refl=> exact banquet.mpr (by rw[sub_self]; exact isLittleO_zero ..)
     | @step j hj ih=>
        refine Serves.trans (banquet.mpr (?_)) ih; let E:=diners L U
        let A:=fun i:ι×Points n=> mote D (j+1) i.2 (θ i.1) T; let B:=fun i:ι×Points n=> mote D j i.2 (θ i.1) T
        have hv:= ( ( guise (expense p h (Nat.lt_succ_of_le hj)) ).comp_tendsto plot_le ).mul_isBigO (Path.cost (L:=L) W K M s v (j+1) T)
        refine ( hv.congr (fun i=>?_) (fun i=> mul_one _) ); change ↑( ((θ i.1)^(j+1)):ℝ )*_=A i-B i; unfold A B Path.mote; rw [Finset.sum_range_succ,Complex.ofReal_pow]; exact ( add_sub_cancel_left .. ).symm
-- curriculum Σ: candidate family Turn across each horizon, meets θ. W.S.Pose & Warp
structure Lamp (G:Gauge) (I:Type) (L:Filter I)(θ:I→ℝ) (X:I→∀ d,View G d) (V:Store G): Prop where
     paid : Tendsto θ L (𝓝 0)
     regular (d n:ℕ)(v:Tags G d n): ∀ᶠ i in L,ContinuousOn (fun y=> X i d n y v) (conf n)
     gleans (d:ℕ): ∃ P:I→Prediction G d,(∀ n (φ:Test n)(v:Tags G d n),∀ᶠ i in L,φ.applyTo (fun y=>X i d n y v)= P i n φ v) ∧ ∀ᶠ i in L,(V.measure d).D (P i)=(V.measure d).D (reference G d)
     rooms (d a n:ℕ)(u:d≤a)(v:Tags G d n): ∀ᶠ i in L,EqOn (fun z=>X i d n z v) (fun z=> X i a n z (Normalize.up u ∘ v)) (conf n)
variable {X:ι→∀ d,View G d}{h:ℕ}
abbrev faceW (X:ι→∀ d,View G d)(i:ι)(u:Rose.Badge)(x:Points 3):ℂ:= X i 6 3 x ( Vials G u )
local notation "X₀"=> (faceW X)
abbrev Place:= Σ n:ℕ, {U:Set (Points n)// Roi U}
def Syllabus (W:Initialize G)(K:Rose.Pick V)(L:Filter ι)(θ:ι→ℝ)(X:ι→∀ d,View G d): Prop:=∀ p:ℕ,0<p→∀ d:ℕ,6≤d→ ∀ P:Finset Place,
    ∃ (τ:ι→ℝ) (b:ℕ)(f:ι→ FieldEnd G d)(q:ι→Veto.caps G) (U:ι→Point G d 2)(a:Axis), IsEquivalent L τ θ ∧ p≤b ∧ Veto.Marque a L (θ^p) q U ∧ f=(fun i=> q i d) ∧ ∀ Y∈P,∀ t:Tags G d Y.fst, Serves L (fun i x=> X i d Y.fst x t) (fun i y=> Path.mote (FVA2.Scale.Measure.start W K d) b y (τ i) (f i ∘ t)) Y.snd.val (θ^p)
-- distinction Φ menu vs root cost needs Φψ for Gram.Margin of support.B.Context
local notation "E(x)" => Rose.test x
abbrev anchorL {n:ℕ} (φ:Test n):Place:= ⟨n,tsupport φ,Testi φ⟩
variable (C:Lamp G ι L θ X V)(E:Syllabus W K L θ X)
include C E
-- Main induction step existence through p
lemma obtainsT (p:ℕ) (u:0<p)(d:ℕ) (w:6≤d) (P:Finset Place) :
    ∃ (τ:ι→ℝ)(b:ℕ),IsEquivalent L τ θ ∧ p≤b ∧ (clockW K X₀-τ)=o[L](θ^p) ∧ ∀ Y∈P,∀ t:Tags G d Y.fst, Serves L (fun i x=> X i d Y.fst x t) (fun i y=>Path.mote (FVA2.Scale.Measure.start W K d) b y (τ i) t) Y.snd.val (θ^p):=by
    let r:= V.survey d; let pB:=anchorL (Rose.test K); let Q:= insert pB P ∪ ( Finset.univ.image (fun i:Fin r.n=> anchorL ( r.scope i ).t) ); obtain ⟨τ,b,f,hM,P',a,he,hp,U,hz,read⟩:=E p u d w Q; let D':= FVA2.Scale.Measure.start W K d; let δ:=θ^p; let Z (i):= Veto.deform ( hM i d ); let h0:= he.symm.tendsto_nhds C.paid
    have hv (Y:Place) (h:Y∈Q)(x:Tags G d Y.fst) : Serves L (fun i y=> X i d Y.fst y x) (fun i y=> mote D' b y (τ i) (stand (Z i) ∘ x)) Y.snd.val δ:=by
       have x':= read Y h x; rw [hz] at x'; refine x'.trans (Path.cash W K M s Y.snd.property (stop h0) (fun i=> income (U.limits (x i))) (fun i=> income (Veto.steered U (x i))) (fun i=> Veto.actReform U (x i)) b)
    obtain ⟨Φ,α,β⟩:= C.gleans d; let G' (j:Fin r.n): Place:= anchorL (r.scope j).t
    have hδ:Inventory L Φ K τ δ b Z Y:= Lesson.issues W K M s U.paid h0 (Veto.stake U) β (C.regular d) α ( fun i=> hv (G' i) (by unfold G' Q; exact Finset.mem_union_right _ ( Finset.mem_image_of_mem _ (Finset.mem_univ _) )) _ )
    have h₁ (Y:Place)(h:Y∈Q)(t:Tags G d Y.fst): Serves L (fun i x=> X i d Y.fst x t) (fun i y=>mote D' b y (τ i) t) Y.snd.val δ:= ordeal W K M s hδ Y.snd.val Y.snd.property _ _ ( hv Y h t )
    have H (x:Rose.Badge): Serves L (fun i=>X₀ i x) (fun i y=> Path.mote (FVA2.Scale.Measure.start W K 6) b y (τ i) ( Vials G x )) pB.snd.val δ:=by
       let u₀:= Vials G x; let U₀:= up w ∘ u₀; refine Serves.fix (h₁ pB ( Finset.mem_union_left _ (Finset.mem_insert_self ..) ) U₀) ( (C.rooms _ _ _ w u₀).mono fun i p=> p.symm.mono pB.snd.property.2 ) (Eventually.of_forall fun i y hy=> Eq.symm (?_)); exact ( Path.pollen _ (⟨y,pB.snd.property.2 hy⟩:Stage 3) u₀ (τ i) b ).trans (( Drawing.increases (q:=b) W K s M u₀ w (⟨y,pB.snd.property.2 hy⟩:Stage 3) (τ i)).trans ( Path.pollen _ (⟨y,pB.snd.property.2 hy⟩:Stage 3) U₀ (τ i) b ).symm )
    refine ⟨τ,b,he,hp, Lark.fortune _ _ M s X₀ h0 U.paid (expense h0 he (Nat.lt_succ_of_le hp)) H (eventually_all.mpr fun p=> C.regular 6 3 (Vials G p)) (lt_of_lt_of_le u hp), fun Y h t=> h₁ Y ( Finset.mem_union_left _ (Finset.mem_insert_of_mem h) ) t ⟩
lemma earned : IsEquivalent L ( clockW K X₀ ) θ:=by
    obtain ⟨τ,b,h,ht,H,_⟩:= obtainsT W K M s C E 1 one_pos _ le_rfl ∅; rw [pow_one] at H; have he:τ+(clockW K X₀-τ)=clockW K X₀:=by abel
    have hv:= h.add_isLittleO H; rwa[he] at hv
lemma completed (p:ℕ)(d:ℕ){U:Set (Points n)} (h:Roi U)(t:Tags G d n)(hp:6≤d): Serves L (fun i x=> X i d n x t) (fun i x=>Path.mote (Measure.start W K d) p x (clockW K X₀ i) t) U ( (clockW K X₀)^p):=by
    let ψ:=clockW K X₀; let P:Place:=⟨n,U,h⟩; obtain ⟨τ,b,hτ,w,h₀,H⟩:= obtainsT W K M s C E (p+1) (Nat.zero_lt_succ p) d hp {P}; let Z:= FVA2.Scale.Measure.start W K d; have he:=earned W K M s C E
    have hm: Serves L _ _ U (θ^(p+1)):= H P ( Finset.mem_singleton_self _ ) t; let hQ:= he.symm.tendsto_nhds C.paid; exact Serves.trans ( ( Serves.trans hm ( orbit_price _ _ M s h (stop hQ) (stop ( hτ.symm.tendsto_nhds C.paid )) h₀ t b ).symm ).up ( powerT C.paid he.symm ( Nat.le_succ _ ))) (lessen _ _ M s h hQ t IsEquivalent.refl ( (Nat.le_succ p).trans w ))
lemma authored (p:ℕ){U:Set (Points n)} (h:Roi U)(t:Tags G d n): Serves L (fun i x=> X i d n x t) (fun i x=> mote D p x (clockW K X₀ i) t) U ((clockW K X₀)^p) :=by
    let a:= d+6; let k:= Nat.le_add_right d 6; let v:= up (G:=G) k; refine Serves.fix ( completed W K M s C E p a h (v ∘ t) (Nat.le_add_left 6 d) ) (( C.rooms d _ _ k t ).mono fun i u=> u.symm.mono h.2 ) (Eventually.of_forall fun i x hx=>?_); let w:Stage n:= ⟨x,h.2 hx⟩; let τ:= clockW K X₀ i; change Path.mote _ p w.val τ _ = _; exact (Path.pollen _ w (v ∘ t) τ p).trans ((Drawing.increases W K s M t k w _).symm.trans ( Path.pollen D w t τ p ).symm)
end Wipe
end YM.SignedWilsonExpansion.Belle

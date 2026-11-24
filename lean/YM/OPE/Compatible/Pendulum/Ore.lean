import YM.OPE.Compatible.Pendulum.WindowView
import YM.OPE.Compatible.Maestro.UniformGrid
/-!
# The chosen joint pair survives OPE schedule
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open Next.Rank.Spindle Next.UVStress
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F K:Finset X}{m j s':X→ℕ}{l:ℕ→ℕ}
   {G:Gauge}{C:Family G}{L:Extraction.Order}{A:Allot C} {W d e k n J b s t:ℕ}
    {y:X→ Cover}(S:Wave m U K (k+1))(S':Wave m K F k)(x:brim D F)(hP:x.val∈brim D K)(hX:x.val∈U)
set_option quotPrecheck false
local notation "H!"=> places X+Fintype.card (C.labels.level d).Index
local notation "Z"=>fun N p i=>Cells.location C.S W N p (y i)
local notation "Ψ"=> fun (N p:ℕ)(i:X)=> Cells.location C.S W N p (y i - y x.val)
local notation "j'"=>fun a=>min (j a) (m a)
local notation "μ"=>fun i=>81*(l i+1)
variable (v:brim D U→ C.book.Token)(u:brim D U→ℝ){r Q a c z:ℝ}
local notation "Y"=>fun i:brim D U=>Run.Below C.path (u i) (s' i.val+1) (finishAt D m i.val)
local notation "q"=> fun i:brim D U=>(v i).1
local notation "F!"=>fun i:brim D U=>(v i).2
structure Mining (D:Origin X)(C:Family G)(U:Finset X)(v:brim D U→ C.book.Token)(x:X)(y:X→ Cover)(N p W J k n d e:ℕ)(T:C.label d)(V:C.label e)(R R' s t:ℝ) : Prop where
    pay : Next.UVStress.quota C d k N p T ≤ R
    support : Cards.PaidAt C.S N p J (C.beta N p) R' (shop D (fun i:brim D U=>(v i).1) (fun i=>(v i).2) x (fun i=>Cells.location C.S W N p (y i-y x)) T)
    tell : Next.UVStress.quota C e n N p V≤ s
    edge : Cards.PaidAt C.S N p J (C.beta N p) t ((shop D (fun i:brim D U=>(v i).1) (fun i=>(v i).2) x (fun i=>Cells.location C.S W N p (y i)) T)*peers D (N:=N) (fun i:brim D U=>(v i).1) (fun i=>(v i).2) x (fun i=>Cells.location C.S W N p (y i))-C.O N p V 0)
def TokenMine (D:Origin X)(C:Family G)(L:Extraction.Order)(U:Finset X)(v:brim D U→ C.book.Token)(x:X)(y:X→ Cover)(W J k n d e:ℕ)(T:C.label d)(V:C.label e)(R R' s t:ℝ): Prop:= C.ref d≤ k∧ C.ref e≤ n∧ ∃ f:Filter (ℕ×ℕ),f.NeBot∧ f≤ L.fuse∧∃ w:ℕ×ℕ→ C.label d, Tendsto w f (𝓝 T)∧ ∃ ψ:ℕ×ℕ→ C.label e, Tendsto ψ f (𝓝 V)∧ ∀ᶠ i in f,Mining D C U v x y i.1 i.2 W J k n d e (w i) (ψ i) R R' s t
variable (h:Positioned C D U m j b J W l y)(hj:m x.val=k+1) (hh:j x.val≤ k) (hν:∀ a∈allUp D U,8*‖C.S.gridPoint W (y a-y x.val)‖≤ C.S.a J)
include S S' hP hX h hj hh hν
lemma ore_won (hA:C.Makes)(hg:G.Simple)
    (hk:C.ref d < j x.val)(hb:1≤ b)(ht':d ≤ b)(ht:∀ i,k ≤ i→ 2*(places X+Fintype.card (C.labels.level d).Index)≤ A.r i)
    (hT: Taxes C D U m (fun i=>min (j i) (m i)) (fun i=>81*(l i+1)) k H! b c)
    (hU:∀ i, 0<u i)(hU':∀ i:brim D U,C.ref (v i).1 ≤ s' i.val ∧ s' i.val+1=j i.val)
    (he:0<z)(hw:z≤ feedS D S Y H! c (⟨x.val,hP⟩:brim D K))
    (hK:Stock.Tabs.opens C.path.levels 1 J s)(hK':Stock.Tabs.opens C.path.levels 1 J t)(hz:m ⊥=n+1)(htN:t ≤ n)(hη:s<k)(hh₁ : C.ref d ≤ s)(hh': C.ref e ≤ t)
    (hx:0<r) (hxA:r ≤ c*badge_fee C z k)(hΦ:r*(2*owed C z d k) ≤ c^2 * ballot C k d)(hμ:r*‖alto C.path k d‖*owed C z d k ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels d k)
    (hR: GridApprox.room C.path.levels J n (lensScope C e))(hM:Expenses C D U m (fun i=>min (j i) (m i)) (fun i=>81*(l i+1)) b a) (hl:∀ i,m ⊥ ≤ i→ places X ≤ A.r i)
    (ha:0 < Q)(hY: Q ≤ a^(F.card*(places X+places X))* (Run.Below C.path ((lantern C.path r d k (j x.val))/2) (j x.val) (finishAt D m x.val)*(∏ i∈univ.erase x,feedS D S' (feedS D S Y H! c) H! c i)))
    (φ:Filter (ℕ×ℕ))(hf:φ.NeBot)(hL:φ≤ L.fuse)(hψ:∀ᶠ i in φ,∀ x:brim D U, 2*u x * Next.Rank.Spindle.paid C (v x).1 (j x.val) i.1 i.2 (v x).2 ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (v x).1 (j x.val)):
    ∃ T V, TokenMine D C L U v x y W J k n d e T V (2*owed C z d k) (stakes C J s/lantern C.path r d k s) (2*owed C Q e n) (2*(stakes C J t / rebate C Q e t n)):=by
    have hQ:= dual_marched D S S' x hP hX v u h hj hh hν hA hg hk hb ht' ht hT hU hU' he hw hK hK' hz htN hη hh₁ hh' hx hxA hΦ hμ hR hM hl ha hY
    let R:=2*owed C z d k; let G':=2*owed C Q e n; let s':=stakes C J s/lantern C.path r d k s; let t':=2*(stakes C J t / rebate C Q e t n); let P(i:ℕ×ℕ)(v₀:C.label d × C.label e):= Mining D C U v x y i.1 i.2 W J k n d e v₀.1 v₀.2 R s' G' t'
    let r(i:ℕ×ℕ):=∀ x:brim D U, 2*u x * Next.Rank.Spindle.paid C (v x).1 (j x.val) i.1 i.2 (v x).2 ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (v x).1 (j x.val)
    have hV:∀ᶠ i in L.fuse, r i→ ∃ v,P i v:=by
        rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [L.per.cofinal.eventually hQ] with p hN; filter_upwards [L.mesh.cofinal.eventually hN] with N hx hV; obtain ⟨T,hE,hχ,W,hw,hW⟩:= hx hV; exact ⟨(T,W),hE,hχ,hw,hW⟩
    let Z'(i:ℕ×ℕ):= if h:∃ v,P i v then h.choose else 0; have hF:∀ᶠ i in φ,P i (Z' i):= (hψ.mp (hV.filter_mono hL)).mono fun i hh=>by unfold Z'; rw [dif_pos hh]; exact hh.choose_spec
    have hK':C.ref d≤ k:= hk.le.trans hh; have hN':C.ref e ≤ n:= hh'.trans htN
    obtain ⟨E,hE,hΘ⟩:= quota_stop C hA hK'; obtain ⟨E',hE',hΘ'⟩:= quota_stop C hA hN'
    obtain ⟨f,he,hp,z,hZ⟩:= finite_extract (𝓛:=φ) (Prod.fst ∘ Z') (E*R) (by filter_upwards [hF,((Cards.largeMesh L).eventually_ge_atTop k).filter_mono hL] with i h hv using (hΘ i.1 i.2 (Z' i).1 hv).trans (mul_le_mul_of_nonneg_left h.pay hE))
    obtain ⟨g,hh,hU,Q₀,hQ⟩:= finite_extract (𝓛:=f) (Prod.snd ∘ Z') (E'*G') (by filter_upwards [hF.filter_mono he,((Cards.largeMesh L).eventually_ge_atTop n).filter_mono (he.trans hL)] with i h hv using (hΘ' i.1 i.2 (Z' i).2 hv).trans (mul_le_mul_of_nonneg_left h.tell hE'))
    exact ⟨_,_,hK',hN',_,hU,hh.trans (he.trans hL),_,hZ.mono_left hh,_,hQ,hF.filter_mono (hh.trans he)⟩
end YM.OPE.Arboreal.Pixel

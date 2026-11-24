import YM.OPE.Compatible.Bard.Tale
/-!
# Match validity depends only on paid route conditions, not
exteriors at finer step. Accuracy waits an additional soldered level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Arcade
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells
open scoped Topology BigOperators Classical
variable {X V I G' T : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X) {U F K:Finset X}{m j:X→ℕ}
    [Fintype V][DecidableEq V][Fintype T][DecidableEq T][Fintype G']
    {G:Gauge}{C:Family G}{p N b d k:ℕ}{l:ℕ→ℕ}{A:Allot C} {z e r:ℝ}
variable {P:Ensemble V}{P':Ensemble T}{E:Track C.path V p}{o:X→ Track C.path V p}
    {E':Track C.path T p}{o':X→Track C.path T p} {f:V ↪ T}{a:T→G'}
    (Q: Extra.Histories.Music (C.labels.level d) C.path N p)
variable (L:Arcade C P' f a D U m j N p P E o b l E' o' k)
    (S:Wave m U K (k+1))(S':Wave m K F k) (x:brim D F)(hP:x.val∈brim D K)(hX:x.val∈U)
variable (q: brim D U→ℕ)(v:∀ i,C.label (q i))(u:brim D U→ℝ) (s:X→ℕ)
set_option quotPrecheck false
local notation "h!"=>places X+Fintype.card (C.labels.level d).Index
local notation "M!"=> inlet (W:=(C.labels.level d).Index) D F x.val m k
local notation "Z"=> (C.labels.level d).Index
local notation "Y"=> entered D q v o' P' x.val Q k
local notation "p₀"=>fun i:brim D U=>Run.Below C.path (u i) (s i.val+1) (finishAt D m i.val)
local notation "x'" => (⟨x.val,hP⟩:brim D K)
local notation "R"=> C.path.rep N p
local notation "Q₀" => C.S.a (k+1)^d*(β C (k+1)*(4*(1/z)))
-- useful through continuum pricing as one receipt.
include L S S' hP hX
lemma trained (hL:Solvent (A:=A) Q)(hA:C.Makes)(hG:G.Simple)
    (hk:C.ref d < k)(hn:k+1<N)(hm: j x.val ≤ k)(hb:1 ≤ b)(ht:∀ i,k ≤ i→Fintype.card G'*(places X+Fintype.card (C.labels.level d).Index)≤ A.r i)
    (hT: Taxes C D U m j l k (places X+Fintype.card (C.labels.level d).Index) b e)
    (hy:∀ i:brim D U,C.ref (q i) ≤ s i.val∧ s i.val<N∧ finishAt D m i.val ≤ s i.val+1 ∧ Migrating C.path (s i.val+1) p N (o i.val)∧ 0<u i ∧2*u i* Spindle.paid C (q i) (s i.val+1) N p (v i) ≤ PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels (q i) (s i.val+1))
    (hv:Migrating C.path k p N (o x.val))(he:0 < z)(hw:z≤ feedS D S p₀ h! e x'):
    let u':=spurs D (spurs D Y S) S'
    Integrable (birth (ManyCopies.Names T _) (C.path.rep N p N) u') (prior G _)∧∃ t:Coefficient (C.labels.level d) (C.side k p), t.Format 0 C.params (R k) ∧ (C.labels.level d).coeffSize t.x ≤ Q₀ ∧ t.remBound 0 (R k) (kappa C.path k) Q₀∧∃ V':Lights A P N p M! k b E (o ∘ Wave.columns D (C.labels.level d).Index F x.val), ∃ X', Session P' f V' (gust C.path N p N (birth (ManyCopies.Names T _) (C.path.rep N p N) u') k ((Nat.le_succ k).trans hn.le)) X' (shades' D F x.val a Z) E' (o'∘ Wave.columns D (C.labels.level d).Index F x.val) ∧
       (∀ i:brim D F,i ≠ x → feedS D S' (feedS D S p₀ h! e) h! e i ≤ V'.bottom (.inl i))∧ e*badge_fee C z k ≤ V'.asks (.inl x)∧ Stamp (N:=N) P (C.localSection d) (E k) t (V'.tips (.inl x))∧ (∀ j:Z, e^2*ballot C k d ≤ V'.asks (.inr j) ∧ Stamp (N:=N) P (C.localSection d) (E k) ((Q.tone k).plays (sonnet C Q k j)) (V'.tips (.inr j))) :=by
    intro y
    have hf:m ⊥≤ k:= lt_of_le_of_lt (Series.high D S'.after S'.after.base.base) S'.lower|>.le; have hN:k ≤ N:= k.le_succ.trans hn.le
    obtain ⟨R',X0,hX',hR,hc⟩:= pay_local D L Q hL x.val hX hA hb hk hN hf (ht N hN) q v u s hv hy
    obtain ⟨hI,M,hY,hF,hB,S0,T₀,hT',hV,hJ,hQ,hQ'⟩:= scene D L S S' x' hX x.2 hX' hA hG hn hk.le (L.bed.head.trans_le hf) ht hm hf (fun a=> Run.below_fee _ (hy a|>.2.2.2.2.1)) (fun i=> (hR i).ge) hT he hw -- y def
    exact ⟨hI,M,hY,hF,hB,S0,T₀,hT',fun i hi=> hV i (Subtype.val_injective.ne hi), hJ,hQ,fun j=>⟨(hc j|>.1) ▸ (hQ' j|>.1), (hQ' j|>.2).symm ▸ (hc j|>.2)⟩⟩
end YM.OPE.Arboreal.Arcade

import YM.OPE.Strobe.Nucleus
/-! # Full-history interpretation of tested pair reflection distribution from mesh scene.
Unselected probe, finite volumes, without limit statement. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
variable {φ : Filter I} {k n:I→ℕ}{v w s:I→ℝ}(L: GracesP C φ k n)
local notation "d*" => B
local notation "loc" => (fun i=>C.S.scale (k i))
local notation "a" => (C.path.levels.clock.hatBeta ∘ k)
local notation "sp" => (fun i=>chapter C (k i) (n i))
local notation "κ" => (fun i=>Real.sqrt (C.path.levels.clock.forcedAllowance i))
include H L
def Crossboard (C:Family G)(k n d:ℕ)(v s:ℝ):Prop:= ∀ (N p:ℕ),∀ he:k<N,∀ o:Site (C.side k p), separation o 0=n→∀ w u:C.label d,Spindle.paid C d k N p w≤v→ Spindle.paid C d k N p u≤v→ ‖moment (C.beta N p) (abrade C w N k p 0 he.le*abrade C u N k p o he.le)-scenePair C w u k N p (C.path.levels.budget k|>.B) o‖≤ s
local notation "s'" i=> (s i/6)
local notation "c'" i=> (s i/(4*v i))
lemma solar (T₀:Citizen C W r D) (d:ℕ)(hv:Coins φ (C.S.scale ∘ k) v)(he:∀ᶠ i in φ,0<v i)(hs:Coins φ (C.S.scale ∘ k) s)(ht:∀ᶠ i in φ,0<s i): ∀ᶠ i in φ, Crossboard C (k i) (n i) d (v i) (s i):=by
    obtain ⟨z,hz,hM⟩:= ((eventually_gt_atTop (C.ref 0)).and (rolls H 0 2)).exists; let s₁ i:= s' i; let s₂ i:= c' i
    have hT:= C.S.divergent.comp L.seeks; have hS:Coins φ (C.S.scale ∘ k) s₁:= Coins.div hs (Bi.const 6 (by norm_num) hT); have hx: Coins φ loc s₂:= Coins.div hs (Coins.mul (Bi.const 4 (by norm_num) hT) hv); have hV: ∀ᶠ i in φ,0<s₂ i:= (he.and ht).mono fun i hi=>div_pos hi.2 (mul_pos (by norm_num) hi.1)
    let b (y z:Bool):Bool→Bool:=fun j=> if j then z else y; have hr (pp q' : Bool)(hh:pp=true∨q'=true): ∀ᶠ i in φ, ∀ N p,∀ hN:k i<N,∀ o:Site (C.side (k i) p), separation o 0=n i→ ∀ x y:C.label d, Spindle.paid C d (k i) N p x≤ v i→ Spindle.paid C d (k i) N p y≤ v i → ‖moment (C.beta N p) (writeF C x N (k i) p (B (k i)) 0 hN.le pp * writeF C y N (k i) p (B (k i)) o hN.le q')‖≤ s₁ i:=by
       obtain ⟨p',hp⟩:∃ i,b pp q' i=true:= by rcases hh with hh|hh; exact ⟨false,hh⟩; exact ⟨true,hh⟩
       filter_upwards [bounded_jobs H L (b pp q') false (by simpa using hM) hz d T₀ p' hp hv he hS (ht.mono fun i hi=>div_pos hi (by norm_num))] with i hi N p hN o hQ x y hx hy
       let z':=fun j:Bool=> if j then o else (0: Site (C.side (k i) p)); let f j:= if j=true then y else x; let x' j := writeF C (f j) N (k i) p (B (k i)) (z' j) hN.le (b pp q' j); have he:= hi _ _ hN z' ⟨rfl,by intro i'; cases i'<;> simp [z',hQ,separation_self],by intro i' j'; cases i'<;> cases j' <;> intro h; exacts [False.elim (h rfl),show _ from (separation_comm 0 o).symm ▸ hQ.ge,hQ.ge,False.elim (h rfl)]⟩ f (fun j=>by cases j; exact hx; exact hy)
       have ht : fineJob x' univ=x' false*x' true:=by unfold fineJob; funext i; simp [mul_comm]
       change ‖moment _ (fineJob x' _)‖ ≤ _ at he; rw [ht] at he; exact he
    filter_upwards [ht,he, bolted H L T₀ d 1 hM hz, bounded_jobs H L (fun _:Unit=>true) () (hM.down (le_refl z) (by simp)) hz d T₀ () rfl hv he hx hV,hr true true (by simp), hr false true (by simp), hr true false (by simp)] with i ht he h hx hy hξ hζ; intro N p hk o hh x y hc hd
    let f(z:C.label d):= fun _:Unit=>z; let X' (q:Unit):= (0:Site (C.side (k i) p)); have he₂(v':C.label d)(he:Spindle.paid C d (k i) N p v' ≤ v i): ‖moment (C.beta N p) (writeF C v' N (k i) p (B (k i)) 0 hk.le true)‖≤ s₂ i:=by
       have hh:= hx N p hk X' ⟨rfl,fun i=>by simp [X',separation_self],fun i j h=>False.elim (h (Subsingleton.elim ..))⟩ (f v') (fun _=>he); have hx (F:Unit→ Config G (C.side N p)→ℂ) : fineJob F univ=F ():= by unfold fineJob;funext i;rw [Fintype.prod_unique]
       rw [hx] at hh; exact hh
    refine le_trans (polarized H x y (B (k i)) o hk.le h.rank (by rw [hh]; exact h.gain.trans_le h.paid) hc hd («c'»:=s₁ i) ?_ (he₂ x hc) (he₂ y hd)) (le_of_eq ?_)
    · intro i' j hp; cases i' <;> cases j; simp at hp;exact hξ _ _ hk _ hh x y hc hd; exact hζ _ _ hk _ hh x y hc hd; exact hy _ _ hk _ hh x y hc hd
    unfold s₁ s₂; field_simp; ring
omit L
-- uniform native shells by restricted filter. No `eventual` cut after period unrestricted. Here price parameter t arbitrary β^t both directions.
lemma arc (T₀:Citizen C W r D) (d t e:ℕ) : ∀ᶠ k:ℕ in atTop,∀ n:ℕ, (C.path.levels.budget k).B^8 ≤ n → (n:ℝ) ≤ (C.path.levels.clock.hatBeta k)^e → Crossboard C k n d (C.path.levels.clock.hatBeta k^t) ((C.path.levels.clock.hatBeta k)^t)⁻¹:=by
    let s:= X; let K:ℕ×ℕ→ℕ:= Prod.fst; let n:ℕ×ℕ→ℕ:= Prod.snd; let S:=(Filter.comap K atTop); let A : Set (ℕ×ℕ):={q | B (K q)^8≤ n q ∧ (n q:ℝ)≤ s (K q)^e}; let M:= S ⊓ Filter.principal A; let v:ℕ×ℕ→ℝ:= fun i=> s (K i)^t; have h:Tendsto K M atTop:= tendsto_iff_comap.mpr inf_le_left; have hB:∀ᶠ i in M,i∈A:=  (Filter.Eventually.filter_mono (show M ≤ (Filter.principal A) from inf_le_right) ((eventually_principal).mpr (fun _ h=>h)))
    have hw:Height C.S M (C.S.scale ∘ K) K 1:= ⟨h,tendsto_const_nhds.congr' (((C.S.divergent.comp h).eventually_gt_atTop 0).mono fun i hi=>(div_self («a»:=C.S.scale (K i)) (ne_of_gt hi)).symm)⟩; have hz:= C.S.divergent.comp h; have hp:= hat_price hz hw; have hk:Coins M (C.S.scale ∘ K) v:= Coins.power hp hz _; have hv:∀ i,0<v i:= fun i=>pow_pos (zero_lt_one.trans ((T).fits.delayed _)) _
    have hx:= solar H (show GracesP C M K n from ⟨h,(Cheap.power hp.up hz e).norm_le (hB.mono fun i (hi:i∈A)=> (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le (hi.2.trans (Real.le_norm_self _))),hB.mono fun i (hi:i∈A)=> hi.1⟩) T₀ d hk (Eventually.of_forall hv) (Coins.inv hk) (Eventually.of_forall fun i=> inv_pos.mpr (hv i)); rw [Filter.eventually_inf_principal] at hx
    obtain ⟨u,hu,hU⟩:= hx; filter_upwards [hu] with i hi b he hx; exact hU (show (i,b)∈ K ⁻¹' u from hi) ⟨he,hx⟩
end YM.OPE.Strobe


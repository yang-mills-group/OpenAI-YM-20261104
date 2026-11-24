import YM.Qlocal.Reckoner.Shelters
/-!
 Mask reconciliation, paid volume-uniformly and before selecting the test. Fundamental lemma at front (price real ≤ b). HardPrice extract full parameter receipt preserving strength factors.N.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{s:V→ Support n}{q q':Ray R} {A A' B u v a r t w δ:ℝ} 
-- resident with full K currency. Acts on any history EXACT with these margins.
abbrev Source (G: Gauge) (n:Side) (Ω:Type) (R:Census V) := Ω→Policy G R n
structure Night (X: RG.Rep G n) (s:V→Support n)(F:Source G n Ω R)(q:Ray R) (t v:ℝ): Prop where
   policy x: Authority X.p X.activities s (F x)
   cost : ∃ f:ℕ→ Ray R,Haze (fun i=>(X.activities.forced i).support) X.p.B t f q v∧∀ x i U,CoverP (f i) (F x i U)
lemma Night.narrow {F:Source G n Ω R}(hX: Night X s F q t v)(p:Rental q')(hq:q' ≤ q)(hc:r ≤ t): Night X s F q' r v:= by
 obtain ⟨f,hf,h⟩:=hX.cost; refine ⟨hX.policy,f,Haze.fades p ?_ hc,h⟩; refine ⟨hf.1,fun x=> budget_mono (hf.2 x) (fun i=>?_) (fun i=>?_)⟩
 · split; exact mul_nonneg (bill_nn (hf.1 _) p.oneSize) (Real.exp_nonneg _); exact le_rfl
 split; exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_right (hq j) (hf.1 _ j)) (Real.exp_nonneg _); exact le_rfl
lemma Night.under {F:Source G n Ω R}(hX:Night X s F q t v)(he:v ≤ w): Night X s F q t w := by obtain ⟨f,hf,h⟩:=hX.cost; exact ⟨hX.policy,f,⟨hf.1,fun i=>budget_loosen (hf.2 i) he⟩,h⟩

namespace Scribe
variable {S:Scribe Ω J G n R} {T:Scribe Ω J' G n R} {p:BudgetPoint} {L:Loom K R n}
    (F:Lot K S L) (H:Lot K T L)
variable {o:V→Site n}
omit F
lemma Night.bulk {K':Source G n Ω R}(hP:Proper S X.p s)(hu:Spend S X.p q t w)(hN:Night X s K' q t v)(p:Rental q) : Bulk X s (S.printP K') q t w v:= by obtain ⟨f,hf,h⟩:=hN.cost; exact S.bulk hP p hu hf (fun i x U=>h x i U) hN.policy -- args order
lemma from_bulk {S:Ledger Ω J G n R}{t q}(h0:Ethics X o s S)(h:Bulk X s S q t A B)(p:Rental q): Night X s S.forced q t B:= by
 exact ⟨regard S h0, Parabola.tab S p h⟩
lemma Spend.narrower (h:Spend S p q t v)(p':Rental q')(hq:q' ≤ q): Spend S p q' t v:= by
 obtain ⟨f,hf,h⟩:=h; refine ⟨f,hf,fun u=>budget_mono (h u) (fun i=>?_) (fun i=>?_)⟩
 · split; exact mul_nonneg (mul_nonneg (p'.pos _|>.le) (hf.nonneg _)) (Real.exp_nonneg _); exact le_rfl
 split; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hq _) (hf.nonneg _)) (Real.exp_nonneg _); exact le_rfl
namespace Lot
include F H
variable [Fintype K]{t' κ:ℝ} {d k k' M:ℕ}
-- H.price hazard; v' chosen before re-expression. Includes using masks cleared under simultaneous union. assumption on F T agreement only after mask.Align.
noncomputable abbrev vault (F:Loom K R n) (f:K→ℝ) (i:K) : Ray R := Pi.single (F.tag i) (f i)
local notation "Ψ"=> (F.turns H)
lemma expenses (ha: S.Proper p s)(hb:T.Proper p s)(hv:S.Spend p q a A)(hx:T.Spend p q a A')
    (hL:L.Path d p.B M) (hp:Rental q)(hr:Rental q') (ht:0≤t) (he:0≤a)(hw:0≤w)(hd:∀ i:R.Mode,i.val.Nonempty→ q' i ≤ w*q i) : ∃ f:ℕ→Ray R, Haze (Lot.tents L:Corrections G n).region p.B t f q' (price_Karea (A+A') t w M d) ∧ ∀ x i U,CoverP (f i) (Lot.ink p F H x i U):= by
 obtain ⟨u,hu,hU⟩:=hv; obtain ⟨v,hv,hV⟩:=hx; let f i:= price F u i+ price H v i; let g i := vault L f i; have hf i:0≤ f i:= add_nonneg (sum_nonneg fun j _=>hu.nonneg j) (sum_nonneg fun j _=>hv.nonneg j); have hg(i:K):0≤ g i:= by intro j; unfold g vault; by_cases ht:j=L.tag i; rw [ht, Pi.single_eq_same]; exact hf _; rw [Pi.single_eq_of_ne ht]; exact le_rfl
 have h : Haze L.region p.B t g q' (price_Karea (A+A') t w M d):= by
    have h0 i:bill q' (g i)=q' (L.tag i)*f i:=by unfold g vault Parabola.bill; rw [Finset.sum_eq_single (L.tag i)]; rw [Pi.single_eq_same]; intro j hj hv; rw [Pi.single_eq_of_ne hv]; ring; simp
    refine ⟨hg,fun i=>?_⟩; convert! budget_plus (dispersed F hL hU hp.oneSize ha.length hu.nonneg ht he hr hw hd i) (dispersed H hL hV hp.oneSize hb.length hv.nonneg ht he hr hw hd i) using 1; ext j; simp only [h0]; split_ifs; unfold f; ring; ring; unfold price_Karea; ring
 let μ:K↪ℕ:=⟨pin,pin_injective⟩; let f':= stuff μ g; have hQ i:0 ≤ f' i:=by unfold f'; by_cases hz:i∈Set.range μ; swap; · rw [blank _ _ hz]
                                                                            obtain ⟨i,rfl⟩:=hz; rw [stuffed]; exact h.1 i
 refine ⟨f', ⟨hQ,fun i=>transfer_budget μ ?_ ?_ (h.2 i)⟩,?_⟩
 · intro j; unfold f'; dsimp only; rw [stuffed,show ((Lot.tents L:Corrections G n)|>.region (μ j)) = _ from Lot.extension_ (F:=F) (H:=H) j]
 · intro j hj; unfold f'; dsimp only; split; rw [blank _ g hj]; simp [Parabola.bill]; rfl
 intro x i U; by_cases hz:i∈ Set.range μ; swap; · rw [show ink p F H x i U=_ from (unpin_blank _ _ hz: ink p F H x i U=0)]; exact alto (hQ i)
 obtain ⟨i,rfl⟩:=hz; unfold f'; rw [stuffed, show μ i=pin i from rfl, ink_code,arc]; intro j; rw [Poly.part_send]; split
 next he=> subst j; unfold g vault; rw [Pi.single_eq_same]; exact le_trans (norm_sub_le ..) (add_le_add ((norm_sum_le ..).trans (sum_le_sum fun i _=> hu.visible ha _ _ _)) ((norm_sum_le ..).trans (sum_le_sum fun j _=>hv.visible hb _ _ _))) -- `..` p_i
 next he=> rw [norm_zero]; exact hg _ j
-- grown At. Limb significance.Est.J. Core.Ang.Weight.H.All.Earn.Height
set_option quotPrecheck false
local notation "P₀"=> X.p
local notation "C₀"=> X.activities
variable (W:Bank X.activities X.p.threshold)
    (g:Source G n Ω R)
noncomputable def era : Source G n Ω R:= fun x=> W.store (Lot.tents L) X.p (g x) (ink X.p F H x)
variable [Countable J][Countable J'][Fintype V][Nonempty V]
local notation "K0"=> era F H W g
local notation "Sκ"=> Lot.price_Karea (A+A') (t+δ) w M d
noncomputable abbrev walletK (κ t b:ℝ):ℝ:= t+κ⁻¹*(Real.exp (κ*t+b)-1)
local notation "Θ₀"=> walletK κ B (Lot.price_Karea (A+A') (t+δ) w M d)
variable (hm:∀ i x U, Healthy X.p.threshold (L.region i) U → ∑ j∈F.rows i,S.score x j U=∑ j∈ H.rows i,T.score x j U)
include hm
theorem shelter_now (hs:∀ i,o i∈s i)(hK:X.activities.ForcedFamily X.p)(h:Night X s g q (t+δ) B)
    (ha:S.Proper X.p s)(hb:T.Proper X.p s)(hu:S.Spend X.p q (t+δ) A)(hv:T.Spend X.p q (t+δ) A')
    (p:Rental q)(hr:Rental q') (hL:L.Path d X.p.B M) (ht:0≤t)(hd:0≤δ)(hQ:1≤κ)(hq:q' ≤ q)(hw:0≤w)
    (hH:∀ i:R.Mode,i.val.Nonempty→q' i ≤ w*q i)
    (hM:StellarTree.sites X.p.B * (κ*B+Lot.price_Karea (A+A') (t+δ) w M d) ≤ δ) :
  Night X s K0 q' t (walletK κ B (Lot.price_Karea (A+A') (t+δ) w M d)) ∧ (Ψ).Spend X.p q t (A+A') ∧ (Ψ).Proper X.p s ∧ ∀ x, ((((Ψ).printP K0).taste X o s).leaf x).density=(((S.printP g).taste X o s).leaf x).density:=by
 let Q':= (Ψ); let B0:= era F H W g; let p0:=Lot.tents L (G:=G); let j:=(t+δ); let u:= Lot.price_Karea (A+A') (t+δ) w M d; have h₁:= h.narrow hr hq le_rfl; let he := F.turns_proper H ha hb; have ht₁:0 ≤ t+δ:=add_nonneg ht hd; have hv' := F.turnout H hu hv
 obtain ⟨f,hf,hV⟩:= expenses F H ha hb hu hv hL p hr ht₁ ht₁ hw hH; have hΔ(x:Ω): Changes X.p p0 (markRead (r:=X) (S.printP g) x) (markRead (r:=X) ((Q').printP g) x) (ink X.p F H x) s := ?_
 · have hS:= (Night.bulk ha (hu.narrower hr hq) h₁ hr); have hZ:=(S.authentic ha hs h₁.policy); let hy:= Q'.authentic he hs h₁.policy;
   have hw'(i:ℕ): (p0.region i).Nonempty:= by
      by_cases hv:i∈Set.range (pin:K→ℕ); swap; · rw [show p0.region i={(0:Site n)} from unpin_blank _ _ hv]; exact singleton_nonempty _
      obtain ⟨i,rfl⟩:=hv; rw [show p0.region (pin i)=L.region i from Lot.extension_ (G:=G) (F:=F) (H:=H) i]; exact L.travel i
   obtain ⟨hg,hg',heE,hw,hR⟩:= Parabola.region (S.printP g) (Q'.printP g) rfl hZ hS hy (Night.bulk he (hv'.narrower hr hq) h₁ hr) W p0 (ink X.p F H) hΔ hr f hf hV hK hd ht hw' hQ hM
   exact ⟨(from_bulk (S:=shelter W p0 (ink X.p F H) (Q'.printP g)) hg hg' hr), hv'.narrow p (le_add_of_nonneg_right hd), he, fun x=> (hR x).symm⟩
 rw [show markRead (r:=X) (S.printP g) x=S.send X.p x from funext (S.marked g x),show markRead (r:=X) (Q'.printP g) x=Q'.send X.p x from funext ((Q').marked g x)]; exact parking X.p F H hm ha hb hu hv p ht₁ _
end Lot
end Scribe
end YM.Qlocal.Reckoner

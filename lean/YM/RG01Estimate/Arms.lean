import YM.RG01Estimate.CensorSeals
/-!
 # Corrected exact family output, Cal handed to marker alignments.
 Keep fused Shift data. Can insert empty slots with `Holidays` (separate RG03 charge if masks move).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor.Toft
open Function Filter Set Lattice Wilson RG Progress.DirectedRecipe AnalyticBridge VerifiedReset Collection Averaging Ovens Ovens.Pipes
   Payments Extra.Iteration Pilgrim Push.BetaTransport Push Push.AbsoluteSums
open Quotes Fresco
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X : Listing G n}{d a b:Collection.Source G n}
   {α β τ D Δ w σ C Λ T H k u v ε δ y γ :ℝ} {c : Clip} {R:PathData G}
open Rep

-- fuse with no shrink. on *these* log & soft records. Index future consumers keep enumeration.
variable {F:Tap G n} {L:Pipes G n}

def port (R:PathData G)(c:Clip)(p:BudgetPoint)(L:Pipes G n)(i:ℕ≃L.Pellet) (F:Tap G n)(β τ:ℝ):RG.Rep G n:=⟨R,c,fused i p F,p,β,τ⟩
lemma passed (i:ℕ≃L.Pellet)(h:Ingredients L F p δ w):
   let U:=port R c p L i F β τ; U.activities.Valid p δ w ∧ ∀ V,U.eval V=(trunk R c p L F β τ).eval V * Real.exp (∑' i,F.logarithm i V):=by
   obtain ⟨κ,γ,u,he,hp,hg⟩:= h.pays
   obtain ⟨ha,hb⟩:= Work.H03.answer _ n _ _ i _ _ _ he
   intro U
   refine ⟨⟨⟨he.stamp.regular.smooth,he.stamp.regular.at_flat,he.stamp.regular.vanish⟩,ha,hb,he.stamp.boundE,Work.H02.answer _ n _ _ i _ _ κ γ _ _ hg he hp⟩,fun V=> ?_⟩
   have hf : U.activities.gas p V= (L.pours F).gas p V*Real.exp (∑' i,F.logarithm i V):= Work.H01.answer _ n _ _ i _ _ κ γ _ he hp V
   unfold Rep.eval; change Real.exp _ * U.activities.gas p V=_; rw [hf,← mul_assoc]; rfl

variable (g:G.Simple) (h:Local X p d (u+v) w)(he:Local X p a u w)(hr:Local X p b v w)(hh:b.logRead=d.logRead-a.logRead)
    {hn:20<n.val} (Q:Pilgrim p n hn)(hx:R.Bounds c σ C Λ)(hC: WilsonStartup.Decent c p)(hs:Geo.Width p c σ)
    (hU: u+v + p.threshold^2 * |Δ-delta (X.read d)| + priceWrap G p (Δ-delta (X.read d)) hn ≤ H)
    (hF:Fees G p c σ C α H w δ γ)

def choiceBeta (Q:Pilgrim p n hn) (L:Listing G n)(R:PathData G)(d a b: Collection.Source G n)
     (β τ α Δ:ℝ)(i:ℕ≃(combine Q (shelves L R p)).Pellet)(c:Clip) :=
     port R c p (combine Q (shelves L R p)) i (stamp Q a b d R L c α Δ) (β+α+Δ) (vac d τ)

include g h he hr hh hx hC hs hU hF
lemma standing (τ : ℝ)(i:ℕ≃(combine Q (shelves X R p)).Pellet):
   let V:= choiceBeta Q X R d a b β τ α Δ i c
   V.Lawful σ C Λ δ γ ∧ V.eval=earlyValue X R c p d β τ α ∧
     Inherit.Debits V (excess n) (regularNeed G p c σ C 0 (v+p.threshold^2* |Δ-delta (X.read d)|) +
       priceWrap G p (Δ-delta (X.read d)) hn) ∧
       let Z:= ((shelves X R p).pours (fill X R c p a α (delta (X.read a))))
       Z.RegularFamily p ∧ Z.EBound p (regularNeed G p c σ C α u) ∧ ∃ f:ℕ↪ℕ, excess n=(Set.range f)ᶜ ∧ ∀ j,V.activities.reg (f j)= Z.reg j∧ V.activities.E (f j)=Z.E j:= by
   intro V
   obtain ⟨ht,hL,hK,-⟩:= seals g h he hr hh Q hx hC hs hU hF
   have hh':= passed (L:=combine ..) (R:=R) (c:=c) (β:=β+α+Δ) (τ:=vac d τ) i ht
   refine ⟨⟨hx,hh'.1⟩,funext (fun U=> (hh'.2 U).trans (bless g h he hr hh Q hx hC hs hU hF U)),?_,?_⟩
   · exact (logistics Q (b:=fill X R c p d α Δ) (Δ:=Δ-delta (X.read d)) hL hK).2
   intro Z
   let N:= numbering (Main n); let f:ℕ↪ℕ:=⟨fun i=> N.symm (.inl i),N.symm.injective.comp Sum.inl_injective⟩
   have hf i:N (f i)=.inl i:=N.apply_symm_apply _
   let ζ:= delta (X.read a)
   refine ⟨he.regFamily g hx hC hn α ζ,hL,f,?_,fun i=>?_⟩
   · ext i; change ((N i).isRight=true) ↔ i∈(Set.range f)ᶜ
     rw [Set.mem_compl_iff]; cases he:N i
     next u=> simp only [Sum.isRight_inl,Bool.false_eq_true,false_iff,not_not]; exact ⟨u,show N.symm _=i from N.symm_apply_eq.mpr he.symm⟩
     next v=>
       constructor
       · rintro - ⟨i,rfl⟩; rw [hf] at he; contradiction
       exact fun _=>rfl
   constructor
   · change allot (shelves X R p).reg _ Q.X _ (N (f i)) =_; rw [hf]; rfl
   change ink (fill X R c p a α ζ).regular _ _ (N (f i))=_; rw [hf]; rfl
end YM.RG01Estimate.Censor.Toft

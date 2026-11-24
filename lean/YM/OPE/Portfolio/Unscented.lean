import YM.OPE.Portfolio.Quartet
/-!
# The unprojected (weight zero, no normalization loss) continuations of
any branches of a caught cluster
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Extra.Histories.Relay
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{H:History G}{N p i j b k :ℕ}{F:Labels.Frame G 0}
    {D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)}{ζ ψ w:ℕ→ℝ}
    {W:Worth}{L: Hol G}
local notation "T"=> H.rep N p
set_option quotPrecheck false
variable (B:SectionData F) {X:∀ i:ℕ,Site (H.S.side i p)} {Y:∀ i:ℕ,Cup (H.rep N p i)}{E:Extra.Histories.Music F H N p}
variable (v:Motion)(h:H.Selected)(hp:B.Sound L)(Hc:Studio.Sessions B E b L W ψ D) (hj:b ≤ k) (hb:k ≤ i)(hi:i≤N)
variable {V:Cup (H.rep N p i)} {R A e:ℝ}{F':Coefficient F (H.S.side i p)}
    (hc:Studio.Mantle H N p i B v (X i) F' V) (hV:F'.Format 0 L (H.rep N p i))(hR:F'.remBound 0 (H.rep N p i) (kappa H i) e)(hQ:F.coeffSize F'.x+e ≤ A)
    (hS:4*(1+(H.levels.params i).columns)*A ≤ R)
include h hp Hc hj hb hi hc hV hR hQ hS
lemma unspent (hr: Fiesta H F ζ ψ k) (hx:∀ i':ℕ,k ≤ i'→ i' ≤ i → 0 < w i')(he:∀ i':ℕ,k ≤ i'→ i' < i→ w (i'+1) ≤ w i') (hy: ∀ i':ℕ,k ≤ i'→ i' < i→ X (i'+1)=(H.levels.clock.op i' p).ratio.embed (X i')) (hA:∀ j:ℕ,k ≤ j → j ≤ i→ w j*(4*R) ≤ ζ j): ∃ Y, Program H N p k i X Y w D hi ∧ Y i=V:=by
    obtain ⟨Z,hZ,hφ,hθ,hQ',ht⟩:= commit B h Hc (hj.trans hb) hi hV hR hQ hS
    let t:= dualize H N p E b i Z 0; let v':= -(Z b).a; have ht' :=Hc.sung.earned _ (hj.trans hb) hi; have hf:F.coeffSize v' ≤ 2*R:= (units_id _ ht' v') ▸ hQ'
    have hP:Club H L B ζ ψ k i N p w D t.voice t.cost hi:=by
        refine Sessions.reissue (t':=fun _=>4*R) B Hc (hj.trans hb) hi hj hb hφ hθ ?_ (fun j hk h=> ?_) (fun j hj hi=>(hx j hj hi).le)
        · intro j hk he; let P:= E.tone j; have hh:= Hc.sung.earned j (hj.trans hk) (he.trans hi); let v₀:=(Z j).a; have hm(x): ((Z j).bar E x).x = v₀+x:= ((keys B H N p L E x (hφ.chairs _ (hj.trans hk) he) hh).1).trans (units_id B hh _); have ha:= ht j (hj.trans hk) he
          unfold Relay.Solo.cost; change _+P.charge (v₀+0)+_ ≤ _; rw [hm,add_zero,show P.charge _= _ from zero_ch B hh v₀,add_zero]
          have h':(Z j).cost E (-(Z b).a)=(Z j).bill:=by unfold Relay.Solo.cost; rw [zero_ch B hh,add_zero]
          rw [h',hm] at ha; let y:= (Z j).bill; have hR:0≤y:= rem_nonneg (hφ.chairs _ (hj.trans hk) he|>.cost); change y+F.coeffSize (v₀+v') ≤_ at ha; have hρ:F.coeffSize v₀ ≤ F.coeffSize (v₀+v')+F.coeffSize v':=by
             nth_rw 1 [show v₀=v₀+v'+ -v' from by abel]; simpa only [show F.coeffSize (-v')=F.coeffSize v' from (by simp [Labels.Frame.coeffSize])] using Size.add F (v₀+v') (-v')
          linarith only [ha,hf,hρ,Work.G08.size_nonneg F (v₀+v'),hR]
        simpa [alto_norm] using! hA j hk h
    obtain ⟨Y',hP,hX⟩:= Program.agenda B v h hp Hc hj hi hr hx he hy hP
    let Q:=E.tone i; have hF(w):= ht'.earns w
    have hu : Studio.Mantle H N p i B v (X i) (Q.plays 0) 0:=by
       have hu:IsLinearMap ℂ (fun v=> (Q.plays v).exponentialEntry 0 B (T i)):= expoLinear _ _ ht'.book (fun w=> (hF w).2) ; -- inference
       refine ⟨?_,?_⟩
       · let p_ : F.Coeff→ Config G (H.S.side i p)→ℂ:=fun v=> (Q.plays v).exponentialEntry 0 B (T i); have ht:p_ 0=0:= (IsLinearMap.mk' p_ hu).map_zero; unfold radiant; rw [show (Q.plays 0).exponentialEntry 0 B (T i)=0 from ht]; simp_rw [show stepUp v (X i) (0:Config G (H.S.side i p)→ℂ)=0 from funext (fun _=> scalar_z _),smul_zero]; rfl -- `..`
       have ht: IsLinearMap ℂ (fun v:F.Coeff=> profile (T i).activities (Q.plays v).forced):= inkL _ _ ht'.book (fun v=> (hF v).2); have hp := (IsLinearMap.mk' _ ht).map_zero; unfold sunny;rw [show profile _ (Q.plays 0).forced= _ from hp,show floatUp v (X i) (0:Res G (H.S.side i p))=0 from funext (fun _=> funext (fun _=> scalar_z _)),smul_zero,Cup.leaves_zero]
    have hx:= (Hc.paidPastel B (hj.trans hb) hi hV hR v hc hu); rw [add_zero] at hx
    refine ⟨Y',hP,(Studio.Mantle.same B v (hX i hb le_rfl) ?_)⟩
    change Studio.Mantle _ _ _ _ _ _ _ ((Z i).bar E 0) _; rw [hZ]; exact hx
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree

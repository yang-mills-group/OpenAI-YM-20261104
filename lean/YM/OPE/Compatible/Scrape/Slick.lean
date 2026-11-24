import YM.OPE.Compatible.Scrape.Tarps
import YM.Next.RANK.Helix
/-!
# Accurate on near links up to scaled logs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source WilsonStartup Gauge Next.Fluctuations Metric Beamer
open MultiNext.SignedSource Lyre Mom Pill
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}
def outing (U:Config G n)(p:Site n):= incG (expandAt o U) (lift (p-o))
abbrev OriginU (U:Config G n) := Lattice.gauge (outing o U) U
lemma sightU (h:2*(b+1)<n.val)(U:Config G n)(i:Dim o b): OriginU o U i.val= Scav (expandAt o U) (register h i).val:=by
     let j:=register h i
     have he(x:Cover)(hx:x∈box b):outing o U (wrap n x+o)=incG (expandAt o U) x:=by rw [outing,add_sub_cancel_right,borne h x hx]
     have ht : OriginU o U i.val=expandAt o (OriginU o U) j.val:=Eq.symm (congr_arg (OriginU o U) (publish h i)); unfold OriginU at *; rw [ht, expandAt_gauge]; change outing o U _ * _*(outing o U _)⁻¹= _; rw [he _ j.property.1,he _ j.property.2]; rfl
lemma brushQC (h:2*(b+1)<n.val)(K:BudgetPoint)(U: Config G n)(P:Pad G) {f:Config G n→ℂ}(hf:K.Regular (Spindle.patch b o) f) (he:∀ i:Dim o b,G.chord (OriginU o U i.val) ≤ P.B) :
      HeadU o h K f (InLine b (K.threshold⁻¹ • board (expandAt o U)))=f U:=by
      let x:= InLine b (K.threshold⁻¹ • board (expandAt o U)); let u:=InLine b (board (expandAt o U)); change HeadU o h K f x=f U; rw [revalue,show (K.threshold • x)= u from by unfold x u; rw [map_smul,smul_inv_smul₀ K.threshold_pos.ne'],←hf.symmetry (outing o U) U]
      -- rw rewrites all f U only?
      apply hf.sites; intro i hi hj; let p:Dim o b:=⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hj⟩⟩; rw [cssh]; have ht :G.curvature (OriginU o U i)= WingB o h u i :=by rw [show OriginU o U i= _ from sightU o h U p]; change _=offsetDir o h i u; rw[offsetDir,dif_pos p.property]; exact (CurU ..).symm
      change _=OriginU o U i; rw [← ht]; exact P.solves _ (he p)
lemma brightD (P:Pad G) (h:2*(b+1)<n.val)(K:BudgetPoint)(U: Config G n){f: Config G n→ℂ}(hf:K.Regular (Spindle.patch b o) f) (he:∀ i:Dim o b,G.chord (OriginU o U i.val) ≤ P.B)(ht: burnU (InLine b (K.threshold⁻¹ • board (expandAt o U))) ≤ P.r^2/2):StartP o P h K f (InLine (4*b) (K.threshold⁻¹ • board (expandAt o U)))=f U:=by
       unfold StartP LaunchB; let v:=K.threshold⁻¹ • board (expandAt o U); rw [homeB,show liftP b (K.threshold⁻¹ • board (expandAt o U))=InLine b v from ?_,minted P _ ht, one_smul]; exact brushQC o h K U P hf he
       have hx:risingO v=v:= sourceU ..; funext i; change royal i.val v=indexS i.val v; rw [champ,hx]
-- uniform local small certificate. Use Helix.impulse. Larger halo
abbrev Belts (b:ℕ):ℝ:= 8*b+1
lemma flushG {U:Config G n}(a:ℝ)(hv:0 ≤ a) (he:∀ i:Dim o (4*b), G.chord (U i.val) ≤ a) :∀ i:TilesB b,G.chord (Scav (expandAt o U) i.val) ≤ Belts b*a:=by
     let x:=expandAt o U; have ht(i:TilesB (4*b)): G.chord (x i.val)≤ a:=he (Spindle.reads i o); have hx(i:Cover)(h:i∈box b): G.chord (incG x i) ≤ (4*b:ℝ)*a:=by
          refine (Tapes.impulse _ hv ?_).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Vibe i h) hv); intro p hp hQ; exact ht ⟨p,Tumb i h p.1 hp,Tumb i h _ hQ⟩
     intro i; apply le_trans (G.chord_triangle (incG x i.val.1*x i.val) _); rw [G.chord_inv]; apply (add_le_add ((G.chord_triangle ..).trans (add_le_add (hx _ i.property.1) (ht ⟨i.val,voles (by omega) i⟩))) (hx _ i.property.2)).trans; unfold Belts; exact le_of_eq (by ring)
lemma braceY (P:Pad G) (h:2*(b+1)<n.val)(K:BudgetPoint)(U:Config G n)(a:ℝ)(ha:0≤a)(he:∀ i:Dim o (4*b),G.chord (U i.val)≤ a)(hp: Belts b*a≤ P.B)(hk:sizeQ b *(K.threshold⁻¹*(Belts b*a))^2 ≤ P.r^2/2): ∀ (f: Config G n→ℂ) (_:K.Regular (Spindle.patch b o) f),StartP o P h K f (InLine (4*b) (K.threshold⁻¹ • board (expandAt o U)))= f U:=by
       intro f hF; let x:= expandAt o U; apply brightD o P h K U hF; · intro i; rw [sightU o h]; exact (flushG o a ha he _).trans hp
       apply (burnhi _).trans; apply le_trans _ hk; refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by unfold sizeQ; positivity); rw [map_smul,norm_smul_of_nonneg (inv_pos.mpr K.threshold_pos).le]; apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr K.threshold_pos).le; refine (pi_norm_le_iff_of_nonneg (mul_nonneg (show 0≤Belts b by unfold Belts; positivity) ha)).mpr ?_; intro i; change ‖indexS i.val (board x)‖ ≤ _; rw [CurU x i.val]; exact (G.curvature_norm _).trans (flushG o a ha he _)
end YM.OPE.Spells

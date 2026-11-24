import YM.SignedWilsonExpansion.F9.Spiro
import YM.SignedWilsonExpansion.F9.Near
/-!
# A complete unit at the publication desk

Before projection `launch` includes literal one and all lower ranks. Verify on both
 roots, so can use exact normalization columns. It faces no ζ timing.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Wheel.Mark (pieceO piece_auth)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{W:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p n :ℕ}
variable {ρ:ℝ}{F:Labels.Frame G h}{L:Frames G}
lemma wt_zeroH (F:Frame G h): wt F 0=0:= congr_arg Prod.fst F.zero_degree
lemma wr_unitH (F:Frame G h): wr F 0=0:= congr_arg Prod.snd F.zero_degree
lemma wr_scalar (F:Frame G h)(i:F.Index)(v:wr F i=0): i=0:= by by_contra u; exact (ne_of_gt (F.factors_pos i u)) v
lemma wt_of_r (F:Frames G)(i:(F.level h).Index) (v:wt (F.level h) i=0): i=0:=by
    let T:=F.level h; apply wr_scalar; apply Nat.eq_zero_of_le_zero; set x:= downL F (d:=0) (Nat.zero_le _) i v.le; have hx:=value_le (F.level 0) x; exact (congr_arg Prod.snd (down_grade F (d:=0) (Nat.zero_le _) i v.le)).symm.trans_le hx
lemma ascendsUnit (L:Frames G)(t:k≤h): upL L t 0=0:= by
    apply wr_scalar; exact (congr_arg Prod.snd (up_grade L t 0)).trans (wr_unitH _)
lemma realM_unit (F:Frame G h)(s:Signed)(i:F.Index): realM F s i 0=if i=0 then 1 else 0:=by
    change (F.act s.ortho _ i).re=_; rw [← show F.coords (Labels.unit G h)=Pi.single 0 (1:ℂ) from F.coords_unit,Frame.act_coords, show tensor s.ortho (Labels.unit G h)=Labels.unit G h from Subtype.ext (map_one (rotated s.ortho)),F.coords_unit]; by_cases p:i=0 <;> simp [Frame.e0,p]
section pin
variable (H:Hol G)(Lp:Frames G)(R:∀ h,Rays G h H)(Rho:∀ h,Survey G H h)
private def knob : Pill G:= Pill.curlP (Rho 0) (Labels.unit G 0) (Labels.unit_grade 0)
private lemma knob_one : (knob H Rho).f=fun _=>1:=by
    funext i; change Complex.re (Labels.read _ (1:Labels.Pol G))=1; rw [map_one]; rfl
private lemma knob_ink (s:Signed): (knob H Rho).spins s=knob H Rho:= Cloth.same _ _ (show ((knob H Rho).spins s).f=(knob H Rho).f from by funext i; simp only [Pill.spins,Function.comp_apply,knob_one]) (show ((knob H Rho).spins s).rank= _ from rfl)
private lemma over_eq (p q:Pill G)(P:p.rank≤k)(Q:q.rank≤k)(he:p=q): Cloth.overC p P 0=Cloth.overC q Q 0:=by subst q;rfl
private lemma unit_nest (i:(Lp.level h).Index)(u:wt (Lp.level h) i=0) (w:wr (Lp.level h) i=0):
    Cloth.raiseC (k:=k) (show wr (Lp.level h) i≤k from w.trans_le (Nat.zero_le _)) (elder Rho R Lp i)= Cloth.overC (knob H Rho) (Nat.zero_le _) 0:=by
    let F:= Lp.level h; let j:=((Lp.level h).bound i); let e:= wt F i; let p:=wr F i; let x:=downL Lp j i (le_refl e); let T:=(Lp.level e); have hx: (T.basis x)∈ Grade (e,p):=by
       rw [← show T.grades x= (e,p) from down_grade Lp j i (le_refl e)]; exact (T.pure x)
    have ht:x=0:= wr_scalar T x ((congr_arg Prod.snd (down_grade Lp j i (le_refl e))).trans w)
    change Cloth.raiseC _ (pricedT (Rho e) (R e) p _ hx)=_
    suffices H':∀ (d r:ℕ)(x':Label G d)(u:x'=Labels.unit G d)(p:x'∈Grade (d,r))(q:r≤k)(_i:d=0)(_k:r=0),Cloth.raiseC q (pricedT (Rho d) (R d) r _ p)=Cloth.overC (knob H Rho) (Nat.zero_le _) 0 from H' e p _ (by rw [ht]; exact T.starts_unit) hx _ u w
    rintro _ _ _ rfl p q rfl rfl; unfold pricedT permitT; simp only [Fintype.sum_empty, Finset.sum_const_zero, add_zero]; rw [Cloth.upRaise]; rfl
lemma launch_card (h:k≤ e)(L:Frames G): Nest H Rho R e k (L:=L) 0=Cloth.overC (knob H Rho) (Nat.zero_le _) 0:=by
    rw [Nest, dif_pos h]; let F:= L.level k; let X:= Cloth.overC (knob H Rho) (k:=e) (Nat.zero_le _) 0; let V:=fetch H Rho R h (L:=L);
    have hX:V 0=X:=unit_nest H L R Rho _ (wt_zeroH F) (wr_unitH F)
    have hv(s:Signed): faux F V (fun s=> Cloth.rotate s e) s 0= X:=by
       unfold faux; rw [Finset.sum_eq_single 0, realM_unit]; · rw [if_pos rfl,one_smul,hX, Cloth.rolled]; exact over_eq _ _ _ _ (knob_ink H Rho s)
       · intro i _ he; rw [realM_unit,if_neg he,zero_smul]
       simp
    unfold notesT bandage; change ((Fintype.card Signed:ℝ)⁻¹) • (∑ s, faux F V (fun s=>Cloth.rotate s e) s 0)=_; simp_rw [hv]; rw [Finset.sum_const, Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma launch_unit (h:k≤e)(L:Frames G): launch L H Rho R e k 0=pieceO G:=by
   unfold launch; rw [Function.comp_apply, launch_card H R Rho h L,Cloth.overD]; apply flash_recover (knob H Rho).solid (piece_auth (j:=0)); intro n; let P:=knob H Rho; have hb:= P.flare n; rw [show P.rank=0 from rfl,pow_zero,one_mul] at hb; rw [show P.reading n=fun _=>1 from funext fun i=> congr_fun (knob_one H Rho) _] at hb; change flash (P.letter.1 n)=flash (uband 1); rw [hb,jet_const,uband_flash,map_one,map_one]
end pin
section stair
-- exact unit reading through every horizon at which it will be used.
variable {H:Hol G}{Z R:ℝ}{S:SectionData F}
lemma rack_sample (i:F.Index)(P: SourceP F)(e): rack F P (pureF F i e)= P i:=by
   unfold rack pureF; rw [Finset.sum_eq_single (i,0)]; · rw [Pi.single_eq_same,one_smul,auxiliary]; change trim (PowerSeries.X^0) _= _; rw [pow_zero]; exact Prod.ext (funext fun n=>affix_plain _) (affix_plain _)
   · intro j _ hj; rw [Pi.single_eq_of_ne hj,zero_smul]
   simp
lemma piece_hi (t:0<e): (pieceO G).2 e=0:=by
   funext r x; dsimp only [Pi.zero_apply]; dsimp only [pieceO]; unfold uband shine; split; simp [PowerSeries.coeff_one, Nat.ne_of_gt t]; rfl
lemma loft_zero (L:Frames G){S:SectionData (L.level 0)}{P:SourceP (L.level 0)} (q:Palette (L.level 0) P k e p Z)(v:Chartage S A Ñ m c N k e p Z)(z:P 0=pieceO G): loftP q v 0=pureF (L.level 0) 0 p:=by
   apply Eq.symm; apply solve_unique _ _ (silent G k); let i₀:(L.level 0).Index:=0; let F:=L.level 0
   rw [zero_add,rack_sample,z]; unfold heard pier; rw [pow_zero,one_smul,calendarUnit v.simple v.ratios v.length v.cap]; funext i; rcases i with ⟨i,j⟩; have hx:i=i₀:= wt_of_r L i (Nat.eq_zero_of_le_zero (F.bound _)); subst i
   by_cases u:j=0
   · rw [u,own,if_pos rfl]; let i:=F.grades i₀; have hx : i=(0,0):= F.zero_degree; change row F ((pieceO G).2 0 (wr F i₀)) _=1
     rw [←z]; exact (q.high (wr F i₀) ⟨i₀,rfl⟩ ⟨i₀,rfl⟩ le_rfl).trans (if_pos rfl)
   unfold pureF output; rw [piece_hi (show 0<j.val from (by have hp:j.val≠0:= fun h=>u (Fin.ext h); omega)),Pi.zero_apply,row_nil,Pi.single_eq_of_ne (fun h=>u (congr_arg Prod.snd h))]
lemma stair_unit {Q:Council L}(H:Hol G)(R:∀ h,Rays G h H)(A':∀ h,Survey G H h) (p:Stair Q (launch L H A' R k) A Ñ m c N h e k v Z)(w:j≤c): p.ladder j 0= pieceO G:=by
    let t:= p.charm 0 (Nat.zero_le _); let P:= p.supply 0 (Nat.zero_le _); let X(i):= launch L H A' R k 0 i; let i:(L.level 0).Index:=0; have hx:X i=pieceO G:=launch_unit H R A' (Nat.zero_le k) L
    rw [← ascendsUnit (h:=h) L (Nat.zero_le h),Stair.on_ladder _ _ _ i (wt_zeroH _)]; change pier A Ñ N 0 k c j (rack _ _ _) = _; rw [loft_zero L P t hx,rack_sample, launch_unit H R A' (Nat.zero_le k) L, pier, calendarUnit t.simple t.ratios w t.cap, pow_zero,one_smul]
end stair
end YM.WilsonCoeffUV.Mer.Xa

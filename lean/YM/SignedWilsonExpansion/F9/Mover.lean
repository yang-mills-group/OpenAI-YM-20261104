import YM.SignedWilsonExpansion.F9.Aroma
/-!
# Singular calibration payer before comparison: reality and filtration
Common motion from WCU and independent bare. Θ preserved through all clock/layout matrices.
Later couple H argument.
-/
set_option autoImplicit false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace Stair
open Cirrus
open Normalize (Sec Formal)
open Tape
variable (W:Initialize G){A'' :∀ h,Rays G h W.hol}{Ω:Council F}{P':Normalize.Store G}
variable (q': Stair Ω (launch F W.hol W.surveys A'' k) A Ñ m c c h e k u Z)
section atDoor
variable (t':Mesh)(ρ:ℝ)
abbrev flagTape (v:d≤h)(i j:(F.level d).Index): InkQ:= insertQ (( t'.spacing^wt (F.level d) j * (sizeT A ρ c^d)⁻¹ ) • q'.Mora v i j)
def printTape (v:d≤h)(i:(F.level d).Index): Tape (Sec G h):=∑ j:(F.level d).Index,Tape.side (Normalize.up v (vista F j)) (flagTape W q' t' ρ v i j)
lemma hingeK (i:(F.level h).Index): q'.bareTape W t' ρ i=q'.printTape W t' ρ ((F.level h).bound i) (downL F ((F.level h).bound i) i (le_refl _)):=by
    let d:=wt Rι i; have h:= (F.level h).bound i; set S:=Finset.univ.image (ownStock F h); unfold bareTape; rw [← Finset.sum_subset (Finset.subset_univ S)]; swap; · intro j _ h'; unfold inkA hymn dye; rw [dif_neg,smul_zero,map_zero,map_zero]; intro v; exact h' (Finset.mem_image.mpr ⟨v.choose,Finset.mem_univ _, v.choose_spec.symm⟩)
    unfold S; rw [Finset.sum_image (stock_faith F h).injOn]; refine Finset.sum_congr rfl fun j _=> ?_; unfold inkA hymn; rw [dye_here,smul_smul]
lemma flagv {d:ℕ}(i:(F.level d).Index) : Normalize.reel d (vista F i)=vista F i:=vista_real ..
lemma tape_permit (i:(F.level h).Index) (x:ℕ): q'.bareTape W t' ρ i x∈ Folia G (wt Rι i) h:=by rw [hingeK,printTape, Finset.sum_apply]; refine Submodule.sum_mem _ (fun i _=>?_); rw [side_read]; exact Submodule.smul_mem _ _ (vista F i).property
lemma bare_real (i:(F.level h).Index) : WReal (q'.bareTape W t' ρ i):=by
    rw [hingeK]; intro j; unfold printTape; simp_rw [Finset.sum_apply,side_read,map_sum,(Normalize.reel _).map_smulₛₗ, flagTape,inked]; refine Finset.sum_congr rfl fun j _=> ?_; rw [show ∀ (a:ℝ),starRingEnd ℂ (↑a:ℂ)=(a:ℂ) from (by simp), show Normalize.reel h (Normalize.up _ (vista F j))=Normalize.up _ (Normalize.reel _ (vista F j)) from rfl,vista_real]
-- support transport of Mora with ground of Motion. full coefficients.
lemma Mora_table (v:d≤h)(s:Signed)(i k':(F.level d).Index): ∑ j,realM (F.level d) s k' j • q'.Mora v i j=∑ j, realM (F.level d) s j i • q'.Mora v j k':=by
   let Q:=F.level d; let P(i):= q'.raft v i; let f:= realM Q s; let u:=q'.charm d v; let g:=q'.supply d v; have hx:=loft_price W.hol g u (manifest W.hol F W.surveys A'' s u.order) i -- parameters
   have hh (m:Fin (e+1)): ∑ j:Q.Index,f k' j * P i (j,m) = ∑ j:Q.Index, f j i*P j (k',m):=by
       have h:= congr_fun hx (k',m); rw [Finset.sum_apply] at h; exact h.symm
   unfold Stair.Mora stamps; simp_rw [Finset.smul_sum,smul_smul]; rw [ Finset.sum_comm]; conv_rhs=> rw [Finset.sum_comm]
   simp_rw [← Finset.sum_smul]; exact Finset.sum_congr rfl fun j _=> congr_arg (fun c:ℝ=> c • _) (hh j)
lemma realM_of (a:ℝ)(x:Cost): insertQ (a • x) = (a:ℂ) • insertQ x := PowerSeries.ext fun i=> by rw [inked, map_smul (coeff (R:=ℂ) i), inked,map_smul]; simp
lemma printB_spin (v:d≤h)(i:(F.level d).Index) (s:Signed): Tape.layer (Normalize.ori s.ortho h) (printTape W q' t' ρ v i)= ∑ j:(F.level d).Index, (realM (F.level d) s j i:ℂ) • printTape W q' t' ρ v j:=by
    let Q:=F.level d; let u(j:Q.Index):= Normalize.up v (vista F j); let b:=realM Q s; let f:=flagTape W q' t' ρ v; let a:=printTape W q' t' ρ v; let z:=fun j:Q.Index=> t'.spacing^wt Q j * (sizeT A ρ c^d)⁻¹; let O:= Normalize.ori (G:=G) s.ortho h
    have hU (x:Q.Index): O (u x)=∑ j:Q.Index,(b j x:ℂ) • u j:=by
       unfold O; rw [show Normalize.ori s.ortho h (u x)=Normalize.up v (Normalize.ori s.ortho d (vista F x)) from rfl,vista_spinner, map_sum]; simp_rw [map_smul]; rfl
    have hv(j x:Q.Index): b j x • (z x • q'.Mora v i x)= z j • (b j x • q'.Mora v i x):=by
       rw [smul_comm]; by_cases u:wt Q j=wt Q x; · unfold z; rw [u]
       rw [show b j x=0 from bleach_sparse _ _ _ _ (fun h=>u (congr_arg Prod.fst h.symm))]; simp
    have ht(x:Q.Index): ∑ j:Q.Index,(b x j:ℂ) • f i j =∑ j:Q.Index,(b j i:ℂ) • f j x:=by
        change (∑ j:Q.Index, _ • insertQ (z j • q'.Mora v i j))=∑ j:Q.Index,_ • insertQ (z x • q'.Mora v j x); simp_rw [← realM_of,hv,←map_sum]; apply congrArg insertQ; simp_rw [← Finset.smul_sum]; calc
            _= z x • ∑ j:Q.Index,b j i • (q'.Mora v j x):= congr_arg (fun g:Cost=> z x • g) (q'.Mora_table W v s i x)
            _=_:=by rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun j _=> smul_comm ..
    funext l; let p(j:Q.Index): ℂ:= coeff l (f i j); have he (j:Q.Index): a j l=∑ x:Q.Index, coeff l (f j x) • u x:=by unfold a printTape; rw [ Finset.sum_apply]; rfl
    change O (a i l)=_; rw [he, map_sum, Finset.sum_apply]; change _= ∑ j:Q.Index,(b j i:ℂ) • a j l; simp_rw [he,map_smul,hU,Finset.smul_sum,smul_smul]; rw [ Finset.sum_comm]; conv_rhs=> rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_smul,← Finset.sum_smul]; have hh:= congr_arg (coeff l) (ht j); simp_rw [map_sum,map_smul,smul_eq_mul] at hh; refine Eq.trans (congr_arg (· • u j) ((Finset.sum_congr rfl fun x _=>mul_comm ..).trans hh)) rfl
lemma own_print (v:d≤h)(i:(F.level d).Index)(p:wt (F.level d) i=d):bareTape W q' t' ρ (upL F v i)= printTape W q' t' ρ v i:=by
    rw [hingeK]; let H:=F.level h; let j:=upL F v i; have ht:wt H j=d:=(congr_arg Prod.fst (up_grade F v i)).trans p
    suffices h : ∀ (t:ℕ)(p:wt H j=t)(u:t≤h), printTape W q' t' ρ u (downL F u j p.le)=printTape W q' t' ρ v i from h _ rfl _
    intro a v1 u; obtain rfl:= v1.symm.trans ht; rw [show downL F v j _=i from up_faith F v (up_down F v j v1.le)]
lemma bare_spin (i:(F.level h).Index)(s:Signed): Tape.layer (Normalize.ori s.ortho h) (q'.bareTape W t' ρ i)=∑ j:(F.level h).Index,(↑(realM Rι s j i):ℂ) • q'.bareTape W t' ρ j:=by
    let f:= q'.bareTape W t' ρ; let q:=wt Rι i; let d:= q; have z:= (F.level h).bound i; let x:= downL F z i (le_refl q); have he:wt (F.level q) x=q:= congr_arg Prod.fst (down_grade F z i (le_refl q)); have hx:upL F z x=i:= up_down ..; set X:=Normalize.ori s.ortho h; let u := q'.printTape W t' ρ z; have t(a:ℝ)(P:Tape (Sec G h)):(a:ℂ) • P=a • P:=by rw [show Complex.ofReal a=a • (1:ℂ) from by simp [Complex.real_smul]]; rw [smul_assoc,one_smul]
    change Tape.layer _ (f i)= _; rw [←hx, show f (upL F z x)=_ from own_print W q' t' ρ z x he, printB_spin]; simp_rw [t]; exact (spectate_weight F s z x he f u (fun j u=>(own_print W q' t' ρ z j u|>.symm))).symm
end atDoor
end Stair
end YM.WilsonCoeffUV.Mer.Xa

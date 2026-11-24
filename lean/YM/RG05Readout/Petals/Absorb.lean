import YM.RG05Readout.Petals.Ingest
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
/-!
# Manifest erasures under multi-charge. Price semantics additive.
 General vectors x only dollar (CAN grow) paid via normalization first in next file. Need actual valuation for residual discrepancy: witness is genuine Stencil bought on SAME extraction, not field projected by FREE. Supports price works before any normalization inside correlation tests. -/
open Dash Extraction Extraction.Lease UVExt -- Avoid `Slots` ambiguity namespace Petals.Slots
namespace Kernel
open UVExt.Slots
variable {P Qz:Trial C}
local notation "I'"=> Fin n
-- d64 D04 transfer rephrased using Manifest. General row comparison.
lemma probes_update (R : Trial C) {I:Fin n→Trial C}(i:Fin n)(a:Fin n→Site (C.side N p)): probes N p n (Function.update I i R) a= moment (C.beta N p) (fun U=> R N p (a i) U*∏ j∈ Finset.univ.erase i, I j N p (a j) U):=by
    unfold UVExt.Slots.probes; congr 1; funext U; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]; congr 1; exact Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
lemma probes_minus {I: Fin n→Trial C}(i:Fin n)(hs:∀ j,Stencilled f (I j))(hP:Stencilled f P)(hQ: Stencilled f Qz) : f.late fun N p=>∀ a:I'→Site (C.side N p), probes N p n (Function.update I i (P-Qz)) a=probes N p n (Function.update I i P) a-probes N p n (Function.update I i Qz) a:=by
   have hv j:= (hs j).sober
   unfold Bid.sober Order.late at hv
   filter_upwards [eventually_all.mpr hv,hP.sober,hQ.sober] with p ha hp hh; filter_upwards [eventually_all.mpr ha,hp,hh] with N hK hx hV a; let P'(U):=∏ j∈Finset.univ.erase i,I j (f.mesh N) (f.per p) (a j) U
   have hu : RG.Envelope P':= Envelope.prodC _ _ (fun j _=> ⟨(hK j _).1,(hK j _).2⟩); simp_rw [probes_update,moment, Pi.sub_apply, sub_mul]; exact integral_sub ((RG.Envelope.mulC ⟨(hx _).1,(hx _).2⟩ hu).integrableC _) ((RG.Envelope.mulC ⟨(hV _).1,(hV _).2⟩ hu).integrableC _)
lemma features_is (q:Fin n→ C.book.Token)(i:Fin n)(a: Fin n→Site (C.side N p)):
    featuring P q i N p a=probes N p n (Function.update (fun j=> Bid.visits C (q j).1 (q j).2) i P) a:=by
    unfold featuring UVExt.Slots.probes; congr 1; funext U; apply Finset.prod_congr rfl; intro j _; by_cases ht:j=i
    · subst j; rw [if_pos rfl,Function.update_self]
    rw [if_neg ht,Function.update_of_ne ht]; rfl
include h
lemma compared (v:Shot C.book)(hp:Stencilled f P)(ht:Stencilled f Qz): ∀ᶠ u in f.fuse,targetB (P-Qz) v u.1 u.2= targetB P v u.1 u.2-targetB Qz v u.1 u.2:=by
    let Y(j):= Bid.visits C (v.left j).1 (v.left j).2; apply Order.fused f _ |>.mpr; exact (probes_minus (I:=Y) v.i (fun i=>Stencilled.visits h _) hp ht).mono fun p hh=> hh.mono fun N hv=> by
       dsimp only; unfold targetB; rw [← mul_sub,← Finset.sum_sub_distrib]; congr 1; apply Finset.sum_congr rfl; intro z _; rw [←mul_sub]; simp_rw [features_is]; exact congr_arg _ (hv z)
lemma quiet {Z:Trial C}(H:UVExt.Slots.manifest Z)(ht:Stencilled f Z) : exactOnSep C f Z:=by
    intro n q i δ hδ; let Y := fun j=> Bid.visits C (q j).1 (q j).2; let X:=Function.update Y i Z; have hx(j):Stencilled f (X j):=by
       unfold X; by_cases he:j=i; subst j; rwa [Function.update_self]; rw [Function.update_of_ne he]; exact Stencilled.visits h _
    refine (erase_manifest h X hx i (by rw [show X i=Z from Function.update_self ..]; exact H) hδ).mono fun p hh=> hh.mono fun i hi x hx=> ?_; rw [features_is]; exact hi x (fun j hj=> hx _ _ hj)

lemma on_profile (x:Rowe C d)(v:Shot C.book)(hx:Reveals C f P x)(hr:CenterPort C f) : Tendsto (fun u:ℕ×ℕ=> targetB P v u.1 u.2-snapshots v d u (x u)) f.fuse (𝓝 0):=by
   obtain ⟨hP,hx,Z,hZ,hσ,y,hy,hq⟩:=hx; let F:=Bid.upper C x
   have hV := Work.D02.answer h hr (P-Z-F) ⟨y,hy, Lease.take h (hr.book ..) hq⟩ v
   have ht : gain Z f (fun _ _=> 0):=fun n q i δ he=>by
       refine ⟨0,le_rfl,(quiet h hZ hσ _ q i δ he).mono fun p hh=> hh.mono fun u hu a hp=> ?_⟩; rw [hu _ hp]; simp
   have hH:= hV.add (Work.D02.answer h hr Z ⟨_,tendsto_const_nhds,ht⟩ v); rw [zero_add] at hH; apply hH.congr'
   filter_upwards [compared h v hP hσ, compared h v (hP.sub hσ) (Stencilled.upper h x)] with i hi hm; rcases i with ⟨N,p⟩; change targetB (P-Z-F) v N p + targetB Z v N p= _ ; unfold F; rw [hm,hi,OPE.Columns.ExtensionCost.upper_scan x v]; abel

-- normalized before any unspent vector pressure
lemma stretched {S:YM.Table C.book}{R:Dash.Bin S}(hp: StrongBin C R f d)(hv:Stencilled f P)(x:Rowe C d)(hc:dollar C f x)(hz:Bid.close C f (Bid.upper C x-P)) :
    let v: Rowe C d:=fun i=>(R d).step i (x i); let b:=fun i:Cutoffs=>(↑((1+‖v i‖)⁻¹):ℂ); Reveals C f (times b P) (fun i=> b i • v i):=by
    intro v b; let w(i):= b i • x i; have hq(i): ‖b i‖≤1:=by unfold b; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]; exact (inv_le_one_of_one_le₀ (by simp))
    have hb:Slow C f b:=(Slow.const (C:=C) (f:=f) (1:ℝ)).reduce (Eventually.of_forall fun i=>by rw [norm_one];exact hq i); have hw: dollar C f w:= (dollar_slow _).mpr (by unfold w; simp_rw [map_smul]; exact hb.smul hc)
    have hwX : (fun i=> (R d).step i (w i))= fun i=> b i • v i:= funext fun i=>map_smul ..
    have hQ: Bid.upper C w-times b P= times b (Bid.upper C x-P):=by
       funext N p t; change C.O _ _ (b _ • _) t- b _ • P _ _ t=b _ • (C.O N p _ t- P _ _ t); rw [(C.linearO ..).map_smul,smul_sub]
    rw [←hwX]; refine produce h hp w hw (stenc_times hv _) ?_ ?_
    · rw [hQ]; exact close_rotate hz b hq
    rw [hwX]; refine ⟨1,Eventually.of_forall fun p=>Eventually.of_forall fun N=> ?_⟩
    dsimp only; unfold b; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity),mul_comm,← div_eq_mul_inv]; exact (div_le_one (by positivity)).mpr (by linarith only)

omit h in
lemma paid_one (s:Shot C.book)(c:Cutoffs→ℂ)(p:ℕ×ℕ): targetB (times c P) s p.1 p.2=c p*targetB P s p.1 p.2:=by
    unfold targetB; rw [mul_left_comm (c p),Finset.mul_sum (a:=c p)]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [mul_left_comm (c p)]; apply congr_arg; simp_rw [features_is, probes_update,moment]; unfold times; simp_rw [Pi.smul_apply,smul_eq_mul,mul_assoc]; exact integral_const_mul ..
variable {T S:YM.Table C.book}{R:Dash.Bin S}{E:DiffPlan T}{L0:ℕ→YM.Table C.book}{I:Type}[Fintype I]{m:ℕ} {v:Cutoffs→C.label d}
-- centered tensor testers. finite set sees vectors of T only.
open Bay
structure Proctor (C:Family G)(f:Extraction.Order){S:YM.Table C.book}(R:Dash.Bin S)(m d:ℕ)(I:Type)[Fintype I](D:I→ Bay.Poem C m)(c:ℝ) :Prop where
   pos : 0<c
   detector : ∀ᶠ j in f.fuse,∀ x:C.label d,(R d).step j x=x → c*‖x‖≤ ∑ i:I, ‖snapshots (D i).sight d j x‖
variable (H:Next.Extract.Base C f S L0 R T E)
omit h
include H
-- need from arbitrary Packet bank,d
lemma proctor (D:I→ Bay.Poem C m)(hV: Injective (LinearMap.pi (fun i=>Poem.passField (D i) T H.kernel.smooth d))):∃ c:ℝ, Proctor C f R m d I D c:=by
     let A:Branch (C.label d) (ℕ×ℕ):=R d; let g (i:I):= (D i).sight.core (d:=d) S H.arrives.born; let X:= fun i:I=> snapshots (D i).sight d; have hp: Tendsto A.step f.fuse (𝓝 A.trueP):= (H.carries d).P
     obtain ⟨L₀,c,hc,hC⟩:= Next.Extract.finite_detectors A.trueP g (fun x hx hK=>by
         have hk(i): (D i).sight.core (d:=d) T ((Bay.Poem.sanctioned H.kernel.smooth)) x=0:= (Dash.faithful H.clean.sharp _ _).symm.trans (hK i)
         have hv: T.project d x=0:= hV (by rw [map_zero]; exact funext fun i=> ((Bay.Poem.intact (D i) H.kernel.smooth (h:=H.kernel.laws.toSymmetric) _).trans (hk _)))
         have ht: x∈T.null d:=(Submodule.Quotient.mk_eq_zero _).mp hv; exact hx.symm.trans ((LinearMap.mem_ker).mp (H.null d ▸ ht)))
     let V i:= ‖A.trueP-A.step i‖ + ∑ j∈L₀, ‖g j-X j i‖; have hx:Tendsto V f.fuse (𝓝 0):=by
       have hr : Tendsto (fun u=> ‖A.trueP-A.step u‖) f.fuse (𝓝 0):= by simpa only [sub_self,norm_zero] using (tendsto_const_nhds (x:=A.trueP)|>.sub hp).norm
       have hb(j:I):Tendsto (fun u: ℕ × ℕ=> ‖g j-X j u‖) f.fuse (𝓝 0):=by
          have ht: Tendsto (X j) f.fuse (𝓝 (g j)):= (D j).sight.ready H.arrives.born H.arrives.census.integral d
          simpa only [sub_self,norm_zero] using (tendsto_const_nhds (x:=g j)|>.sub ht).norm
       exact (show Tendsto V f.fuse (𝓝 (0+∑ j∈L₀,(0:ℝ))) from hr.add (tendsto_finsetSum L₀ fun j _=>hb j)) |>.mono_right (by simp)
     refine ⟨c/2,half_pos hc,?_⟩; filter_upwards [hx.eventually (gt_mem_nhds (half_pos hc))] with u hh x hk
     -- detector_of_good argument
     have hm: c*‖x‖ ≤ V u*‖x‖+∑ i∈L₀, ‖X i u x‖:=by
         have he: ‖A.trueP x -x‖≤ ‖A.trueP-A.step u‖*‖x‖:=by have ht:=(A.trueP-A.step u).le_opNorm x; rw [show (A.trueP - A.step u) x=A.trueP x - A.step u x from rfl,show A.step u x=x from hk] at ht; exact ht
         have hb i:‖g i x‖ ≤ ‖g i-X i u‖*‖x‖+ ‖X i u x‖:=by
             have ht:= norm_sub_norm_le (g i x) (X i u x); exact le_trans ((le_add_of_sub_left_le ht).trans_eq (add_comm ..)) (add_le_add_left ((g i-X i u).le_opNorm x) _)
         unfold V; rw [add_mul,Finset.sum_mul,add_assoc,←Finset.sum_add_distrib]; exact (hC x).trans (add_le_add he (Finset.sum_le_sum fun i _=>hb i))
     apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg (s:=L₀) (Finset.subset_univ _) (fun i _ _=>norm_nonneg _)); have hv: V u ≤ c/2:= le_of_lt hh; change _ ≤ ∑ i∈L₀, ‖X i u x‖; linarith only [hm, mul_le_mul_of_nonneg_right hv (norm_nonneg x)]
-- ... tight next
end Kernel
end YM.RG05Readout.Petals

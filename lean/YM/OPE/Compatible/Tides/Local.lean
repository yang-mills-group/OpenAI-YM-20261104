import YM.OPE.Compatible.Tides.Figo
import YM.OPE.Compatible.Mire.Ova
/-!
# ℝ power kernels on Cover arbitrary t0
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush
open Pert.Full (incVec)
open scoped BigOperators Classical ContDiff
variable {f g:Cover→ℝ}{F G:E4→ℝ}{k j:ℤ}
def quilting (k:ℤ)(f:Cover→ℝ)(n:Side)(x:Cover):=dew n^(-k)*f x
def Quip (k:ℤ)(f:Cover→ℝ)(F:E4→ℝ):Prop :=∀ (n:ℕ→Side)(x:ℕ→Cover), Tendsto (fun i=>(n i).val) atTop atTop→∀ p:E4,p≠0 → Tendsto (fun i=> incVec (dew (n i)) (x i)) atTop (𝓝 p) → Tendsto (fun i=>quilting k f (n i) (x i)) atTop (𝓝 (F p))
lemma Quip.purse (h:Quip k f F)(hp:Quip j g G): Quip (k+j) (f*g) (F*G):=by
   intro n x hn p he hx
   rw [show (fun i=>quilting (k+j) _ _ (x i))=(fun i=> quilting k f (n i) (x i)*quilting j g (n i) (x i)) from funext fun i=>by dsimp only[quilting,Pi.mul_apply]; rw [neg_add,zpow_add₀ (dew_pos _).ne'];ring]; exact (h n x hn p he hx).mul (hp n x hn p he hx)
lemma Quip.fuse (hf:Quip k f F)(hg:Quip k g G):Quip k (f+g) (F+G):=by
    intro n x hn p he hx; simpa only [quilting,Pi.add_apply, mul_add] using! ((hf n x hn p he hx).add (hg n x hn p he hx))
lemma Quip.shiftP (h:Quip k f F)(a:Cover): Quip k (fun x=> f (x+a)) F:=by
    intro n x hn p h' hv; apply h n (fun i=>x i+a) hn p h'; simp_rw [Pert.Band.incVec_twist]
    have he: Continuous (fun r:ℝ=> incVec r a):=by unfold Pert.Full.incVec; fun_prop
    have hb:Tendsto (fun i=> dew (n i)) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn); have hy:= he.continuousAt.tendsto.comp hb
    have hx:incVec 0 a=0:=by ext i;simp
    simpa only [hx,add_zero] using! hv.add hy
lemma Quip_cash (hf:Quip k f F):∃ c≥0,∀ x, ‖f x‖≤ c*(notch x:ℝ)^(-k) :=by
   let H(x:Cover):=‖f x‖*(notch x:ℝ)^k; have hh(x:Cover):0<(notch x:ℝ):=Nat.cast_pos.mpr (notch_one x); by_contra! he
   have hP (i:ℕ): ∃ x:Cover,i≤ size x ∧ (i:ℝ)<H x:=by
       let B:=∑ x∈pod i,H x
       have hx(x):0≤H x:= mul_nonneg (norm_nonneg _) (zpow_pos (hh _) _).le; have hb:0≤B:=Finset.sum_nonneg (fun i _=>hx i); obtain ⟨x,L⟩:=he ((i:ℝ)+B) (by positivity); -- shadow
       have hp:(i:ℝ)+B<H x:=by unfold H; have h0:=mul_lt_mul_of_pos_right L (zpow_pos (hh x) k); rw [mul_assoc,← zpow_add₀ (hh x).ne',neg_add_cancel,zpow_zero,mul_one] at h0; exact h0
       refine ⟨x,?_ ,lt_of_le_of_lt (le_add_of_nonneg_right hb) hp⟩; by_contra! ht; exact not_lt_of_ge ((Finset.single_le_sum (fun x (_:x∈pod i)=>hx x) (in_pod.mpr ht.le)).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))) hp
   choose x hx v using hP; let n(i):Side:=⟨notch (x i), notch_one _⟩; let y(i):=incVec (dew (n i)) (x i)
   have hy(i): dew (n i)*(size (x i):ℝ)=1-dew (n i):=by unfold dew n sizeR notch; change ((↑(1+size (x i):ℕ):ℝ))⁻¹*_=1-((↑(1+size (x i):ℕ):ℝ))⁻¹; push_cast; field_simp;ring
   have hv(i):‖y i‖≤ 2:=by have hp:=dew_pos (n i); unfold y; apply (twice_bead _ _ hp.le).trans; rw [mul_assoc,hy i]; linarith only [hp]
   obtain ⟨p,hp,L,hL,h⟩:= isCompact_closedBall (0:E4) 2|>.tendsto_subseq (x:=y) (fun i=> mem_closedBall_zero_iff.mpr (hv i))
   have hw:Tendsto (fun i=>(n i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (g:=fun i=>_) (fun i=>by have ht:=hx i; change i≤1+_; omega) tendsto_id
   have hh':Tendsto (fun i=>dew (n i)) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hw)
   have he':p≠0:=by
       rintro rfl; have ht(i):1-dew (n (L i)) ≤ 4*‖(y ∘ L) i‖:=hy _ ▸ bead _ _ (dew_pos _).le; have hE:=le_of_tendsto_of_tendsto (tendsto_const_nhds.sub (hh'.comp hL.tendsto_atTop)) (h.norm.const_mul 4) (Eventually.of_forall ht); norm_num at hE
   let A:=F p; have ht:=hf (n ∘ L) (x ∘ L) (hw.comp hL.tendsto_atTop) p he' h
   have ha(i):H (x (L i))=‖quilting k f ((n ∘ L) i) ((x ∘ L) i)‖:=by change ‖f (x (L i))‖*(notch (x (L i)):ℝ)^k= ‖(notch (x (L i)):ℝ)⁻¹^(-k)*f (x (L i))‖; rw [norm_mul,zpow_neg, inv_zpow, inv_inv, Real.norm_of_nonneg (zpow_pos (hh (x (L i))) k).le,mul_comm]
   obtain ⟨i,ht',hv'⟩:= ((ht.norm.eventually (gt_mem_nhds (lt_add_one ‖A‖))).and ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp hL.tendsto_atTop).eventually (eventually_ge_atTop (‖A‖+1)))).exists; exact not_lt.mpr hv' (lt_trans (ha _ ▸ v _) ht')
lemma lineQ (D:List Axis):Quip ((D.length+2:ℕ):ℤ) (hull D) (tint D):=by
   intro n x hn p he hx; simp only[quilting,zpow_neg,zpow_natCast]; exact softening he D _ hn _ hx
end YM.OPE.Balsam

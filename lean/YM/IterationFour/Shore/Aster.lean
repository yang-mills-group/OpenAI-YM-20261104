import YM.IterationFour.Shore.Offers

/-! Top grade estimates in the EXACT startup implementation at every finite
order. Point domain arbitrary. We extend WilsonStartup `Quad` evaluator from
three (constant/surplus only) to arbitrary curvature-taylor entries in the same
k germ; their real-jet bills need only PRE conditions. No substitution for
local RG analytic proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.IterationFour
open Lattice Wilson RG Function MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
open Quad Work Tensor Next.Fluctuations
attribute [local instance] Gauge.frobInner
variable {G : Gauge}{n : Side}{p : BudgetPoint}{f : G.Mat→ℝ}{q k r :ℕ}

/-- Wilson plaquette price entries in actual gauge quotient k. -/
def cir (G:Gauge) (r:ℕ) (x:G.Color):ℝ:= Tensor.diagonal (coeff (inK G) r 0) x
def terms (G:Gauge) (r:ℕ): G.Mat→ℝ:= cir G r ∘ Quad.kMat
/-- Includes Δ deterministic top λ clips via local E dictionary. -/
def chip (G:Gauge) (r:ℕ) (A:G.Mat): ℝ:= Quad.surplusMat A - ((G05.blockTaylor (r+2) (inK G) - G05.blockTaylor 4 (inK G)) (Quad.kMat A))
def element (G:Gauge) (f:G.Mat→ℝ) (p : Cell n) (U:Config G n): ℝ:= f (G.mat (faceValue U p))

lemma chip_sum (G:Gauge) (r:ℕ) (hr:2≤r) (A:G.Mat):
    chip G r A + ∑ j∈ Finset.range (r-2), terms G (5+j) A = Quad.surplusMat A:=by
   let F:= fun i:ℕ=>terms G i A
   simp only [chip, Pi.sub_apply,G05.blockTaylor,Finset.sum_apply]
   change _ - (((∑ i∈ Finset.range (r+2+1),Tensor.diagonal (coeff (inK G) i 0) (Quad.kMat A))- ∑ i∈ Finset.range 5, F i)) + _=_
   rw [show r+2+1=5+(r-2) by omega]; change _-( (∑ i∈ Finset.range (5+(r-2)),F i)- _)+_=_
   rw [Finset.sum_range_add F]; abel

@[fun_prop] lemma terms_diff (G:Gauge) (r:ℕ) : ContDiff ℝ ω (terms G r) := (diag_smooth ..).comp kMat_diff
@[fun_prop] lemma chip_diff (G:Gauge) (r:ℕ): ContDiff ℝ ω (chip G r):= Quad.surplusMat_diff.sub (((G05.blockTaylor_contDiff (r+2) ..).sub (G05.blockTaylor_contDiff ..)).comp kMat_diff)
structure Stamp (f:G.Mat→ℝ) (q:ℕ):Prop where
   globalB : ContDiff ℝ ω f
   cancels : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (u:E→G.El), ContDiffAt ℝ ω (G.mat∘u) 0 → u 0=1→FlatAt q (f ∘ G.mat ∘ u) 0
   conjugate t u:f (G.mat (t*u*t⁻¹))=f (G.mat u)
   reverse u:f (G.mat u⁻¹)=f (G.mat u)
lemma cir_diff (G:Gauge) (r:ℕ): ContDiff ℝ ω (cir G r):= diag_smooth ..
lemma diagonal_even (G:Gauge) (r:ℕ) (x:G.Color): cir G r (-x)=cir G r x:=by
   unfold cir
   cases Nat.even_or_odd r with
   | inl h=> rw [← neg_one_smul ℝ _,homogeneous,h.neg_one_pow]; simp
   | inr h=> rw [odd_diagonal (-x) r h, odd_diagonal x r h]
lemma cir_flat (G:Gauge) (k:ℕ) : FlatAt k (cir G k) 0:=by
    intro j hj
    cases k; · omega
    rename_i k
    let f:=inK G; let J:=G05.blockTaylor (k+1) f; let I:=G05.blockTaylor k f
    have hp: cir G (k+1)= J-I:= by funext v; simp [J,I,cir,G05.blockTaylor,Finset.sum_range_succ _ (k+1), f]
    have h:= (G05.blockTaylor_contDiff (k+1) f (j:ℕ∞ω)).contDiffAt (x:=0) -- args
    rw [hp,iteratedFDeriv_sub_apply h (G05.blockTaylor_contDiff .. |>.contDiffAt)]
    change iteratedFDeriv ℝ j (G05.blockTaylor (k+1) (inK G)) 0 - iteratedFDeriv ℝ j (G05.blockTaylor k (inK G)) 0 = 0; rw [G05.blockTaylor_jets (inK_diff.of_le le_top) _ hj.le,G05.blockTaylor_jets (inK_diff.of_le le_top) _ (by omega : j ≤ k),sub_self]
lemma terms_stamp (G:Gauge)(k:ℕ): Stamp (G:=G) (terms G k) k:= by
    refine ⟨terms_diff ..,fun E h h' u ht hu=>?_,fun t u=>?_,fun u=>?_⟩
    · have he: G.curvature (u 0)=(0:G.Color):=by rw [hu,G.curvature_unit]
      have hK: ∀ v,G.curvature (u v)=Quad.kMat (G.mat (u v)):= fun v=> (k_actual _).symm
      change FlatAt k (fun v=>cir G k (Quad.kMat (G.mat (u v)))) 0
      simp_rw [← hK]
      apply FlatAt.comp (f:=cir G k) (u:=fun i=>G.curvature (u i)); · rw [he]; exact cir_flat G k
      · rw [he]; exact (cir_diff G k|>.of_le le_top).contDiffAt
      exact ((curvature_diff_mat u 0 ht).of_le le_top)
    · unfold terms; dsimp only [Function.comp_apply]; rw [k_actual,k_actual,G.curvature_conjugate]; exact coeff_adjoint ..
    unfold terms; dsimp only [Function.comp_apply]; rw [k_actual,k_actual,G.curvature_inv]; exact diagonal_even ..
lemma chip_stamp (G:Gauge)(r:ℕ)(hr:2≤r):Stamp (G:=G) (chip G r) (r+3):=by
   have hm u: chip G r (G.mat u)=surplus u-∑ i∈ Finset.range (r-2), terms G (5+i) (G.mat u):= by
     rw [← Quad.surplus_actual,← chip_sum G r hr, add_sub_cancel_right]
   refine ⟨chip_diff ..,fun E h h' u ht hu=>?_, fun t u=>by rw [hm,surplus_conjugate,hm]; congr 1; exact Finset.sum_congr rfl (fun i _=> (terms_stamp G _).conjugate ..),fun u=>by rw [hm,surplus_inv,hm]; congr 1; exact Finset.sum_congr rfl (fun i _=> (terms_stamp G _).reverse ..)⟩
   have hc : ContinuousAt u 0 := (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr ht.continuousAt
   let k:=fun i=>G.curvature (u i)
   have he : k 0=0:=by simp [k,hu]
   apply FlatAt.congr (FlatAt.comp (f:=inK G-G05.blockTaylor (r+2) (inK G)) (u:=k) (he.symm ▸ flat_sub_taylor _ _ (inK_diff.of_le le_top : ContDiffAt ℝ (↑(r+2):ℕ∞ω) _ _)) (by rw [he]; exact (inK_diff.of_le le_top).sub (G05.blockTaylor_contDiff .. |>.contDiffAt)) ((curvature_diff_mat u 0 ht).of_le le_top)) -- f annotations
   filter_upwards [(show Tendsto u (𝓝 0) (𝓝 1) from hu ▸ hc.tendsto).eventually (recover_left G)] with x hx
   simp only [comp_apply, Pi.sub_apply, chip,k_actual, convert_taylor,surplus_actual,surplus, k,inK,hx]; ring

/-! Ordered all real jets, shift notations needed since mask is charged on healthy
full fields, not with whole-link smallness. Generalize existing Quad estimate. -/

def lamp (f:G.Mat→ℝ) : List (Quad.Dir G) → Quad.Space G →ℝ
    | [] => f ∘ readMat
    | a::l => fun X=> deriv (fun t:ℝ=>lamp f l (spin (t•a) X)) 0
lemma lamp_diff (h:ContDiff ℝ ω f) (s:ℕ): ContDiff ℝ ω (fun p : (Fin s→ Dir G) × Space G=> lamp f (List.ofFn p.1) p.2):=by
   induction s with
   | zero=> simp only [List.ofFn_zero,lamp]; exact ((h.comp readMat_diff).comp contDiff_snd)
   | succ s ih=>
      let V (p : (Fin (s+1)→Dir G) × Space G) (b:ℝ):= lamp f (List.ofFn (Fin.tail p.1)) (spin (b•p.1 0) p.2)
      have hV: ContDiff ℝ ω (uncurry V):=ih.comp ((contDiff_pi.mpr fun i=> (contDiff_apply ..).comp contDiff_fst.fst).prodMk
        (spin_diff.comp ((contDiff_snd.smul ((contDiff_apply ..).comp contDiff_fst.fst)).prodMk contDiff_fst.snd)))
      simp only [List.ofFn_succ,lamp,deriv]; exact (hV.fderiv (g:=fun _=>0) contDiff_const le_top).clm_apply (g:=fun _=>(1:ℝ)) contDiff_const
lemma lamp_scale (c:ℝ)(l:List (Dir G)) (X:Space G): lamp f (l.map (c•·)) X = c^l.length * lamp f l X:=by
   induction l generalizing X with
   | nil=> simp [lamp]
   | cons a l ih=>
     simp only [List.map_cons, lamp, List.length_cons, ih, smul_smul, mul_comm _ c,
      deriv_const_mul_field, deriv_comp_mul_left c (fun t => lamp f l (spin (t • a) X)),mul_zero,smul_eq_mul,pow_succ]; ring
lemma rooted (h:Stamp (G:=G) f q) (l : List (Dir G)){E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E](U:E→Quad.Group G)(hx:ContDiff ℝ ω (Quad.mat ∘ U))(hp:Quad.read (U 0)=1): FlatAt (q-l.length) (lamp f l ∘ Quad.mat∘ U) 0:=by
   induction l generalizing E with
   | nil=>
      rw [show lamp f ([]:List (Dir G)) ∘ mat ∘ U= f ∘ G.mat ∘ read ∘ U from funext fun x=> by simp only [lamp,comp_apply,read_actual]]
      exact h.cancels _ (read ∘ U) (by simp only [comp_def, ← read_actual]; exact (readMat_diff.comp hx).contDiffAt) hp
   | cons a l ih=>
      let Q (v : E×ℝ) (i:Fin 4):= G.lieExp (v.2•a i)* U v.1 i
      have hm : mat ∘ Q=uncurry spin ∘ fun x=>(x.2•a,mat (U x.1)):= by funext x i; exact G.mat_mul ..
      have hQ: ContDiff ℝ ω (mat ∘ Q):= by rw [hm]; exact spin_diff.comp ((contDiff_snd.smul contDiff_const).prodMk (hx.comp contDiff_fst))
      have hh:= ih Q hQ (by simpa [Q] using hp)
      rw [List.length_cons,← Nat.sub_sub]; change FlatAt _ (fun x=> deriv _ 0) _; refine hh.partial_zero ?_
      rw [← List.ofFn_get l]; exact (lamp_diff h.globalB l.length).comp (contDiff_const.prodMk hQ)
lemma collected (h:Stamp (G:=G) f q) (k:ℕ) (r:ℝ):∃ C δ:ℝ,0<C ∧ 0<δ ∧ δ≤1∧∀ (a: Fin k→Dir G)(U:Quad.Group G)(b:ℝ),0<b→ b ≤ δ→ ‖a‖ ≤ b*r→ G.chord (read U) ≤ b → ‖lamp f (List.ofFn a) (mat U)‖ ≤ C*b^q:=by
   obtain ⟨c,d,hc,hd,hp⟩:= log_chart_cost G
   let L (p : (Fin k→Dir G)×Space G) (x:G.Color):= lamp f (List.ofFn p.1) (reconstruct p.2 x)
   have hL: ContDiff ℝ ω (uncurry L):= (lamp_diff h.globalB _).comp (contDiff_fst.fst.prodMk (reconstruct_diff.comp (contDiff_fst.snd.prodMk contDiff_snd)))
   let K: Set ((Fin k→Dir G)×Space G):= Metric.closedBall 0 r ×ˢ Set.range mat
   obtain ⟨V,hV,hZ⟩:= uniform_flat_price K ((isCompact_closedBall 0 r).prod (isCompact_range (f:=mat) (by unfold mat; fun_prop))) 1 L hL (fun _=> True) (q-k) (by
       rintro ⟨w,u⟩ ⟨-,b,rfl⟩ -
       let P (x:G.Color) (i : Fin 4):= if i=0 then G.lieExp x*b 3*b 2*(b 1)⁻¹ else b i
       have he: reconstruct (mat b)=mat ∘ P:= by ext1 x; ext1 i; unfold reconstruct; dsimp only [comp_apply,mat,P]; split<;> simp[*]
       simp only [L]; simp_rw [he]
       simpa only [List.length_ofFn,Function.comp_def] using! rooted h (List.ofFn w) P (he ▸ reconstruct_diff.comp (contDiff_const.prodMk contDiff_id)) (by simp [P,Quad.read,mul_assoc])) -- check unction
   refine ⟨V*c^(q-k), min (min d c⁻¹) 1, mul_pos hV (pow_pos hc _),lt_min (lt_min hd (inv_pos.mpr hc)) one_pos,min_le_right ..,fun a U b hb he ha hu=>?_⟩
   obtain ⟨hle,hs⟩:= le_min_iff.mp he; obtain ⟨h₁,h₂⟩:= le_min_iff.mp hle
   obtain ⟨hx,hw⟩:= hp (read U) (hu.trans h₁)
   let s:= b⁻¹ • a; have hv:‖s‖ ≤ r:= by
      unfold s; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hb).le]
      exact (mul_le_mul_of_nonneg_left ha (inv_pos.mpr hb).le).trans_eq (inv_mul_cancel_left₀ hb.ne' _)
   have hη:= hw.trans (mul_le_mul_of_nonneg_left hu hc.le)
   have hx':= hZ (s,mat U) ⟨by simpa using hv,Set.mem_range_self U⟩ trivial _ (hη.trans ((mul_le_mul_of_nonneg_left h₂ hc.le).trans_eq (mul_inv_cancel₀ hc.ne')))
   have hz : lamp f (List.ofFn a) (mat U)= b^k * lamp f (List.ofFn s) (mat U):=by
      simpa only [List.length_ofFn,List.map_ofFn, comp_def,s, Pi.smul_apply, smul_smul,mul_inv_cancel₀ hb.ne',one_smul] using! lamp_scale (f:=f) b (List.ofFn s) (mat U)
   unfold L at hx'; simp only [reconstructed U hx] at hx'; rw [hz,norm_mul,Real.norm_of_nonneg (pow_pos hb _).le]; refine (mul_le_mul_of_nonneg_left (hx'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hη _) hV.le)) (pow_nonneg hb.le _)).trans ?_
   rw [mul_pow c b (q-k)] -- fix
   refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb.le hs (show q ≤ k+(q-k) by omega)) (mul_nonneg hV.le (pow_nonneg hc.le (q-k))))
   rw [pow_add]; ring
end YM.WilsonStartup.IterationFour

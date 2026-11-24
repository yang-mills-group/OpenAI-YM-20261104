import YM.Contacts.Milling.Nimbus
import YM.Contacts.Pulse.Jacket
/-! pre-block rank two charge in hybrid spatial norm (including projection and reexpression).
 Also for NOT already Ward/lifted arrays. Direct Laurent moment calculation -/
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {α X Y: Type}{n m:Side}{t k j:ℕ}{b c:ℝ}{G:Gauge}{F:bore G}{s η:ℝ≥0}
section shift
variable {K : Tailor 1→ℝ}(i:Keys 1)
private def tooth (x:Tailor 1)(i:Keys 1):ℂ:= (x i:ℂ)*Complex.I
private def grindA (x:Tailor 1)(i:Keys 1)(t:ℝ) := Laurent.mode (axes (t • Pi.single i (1:ℝ))) x -- axes
private def reed (K:Tailor 1→ℝ)(k:ℕ) (x:Tailor 1)(t:ℝ):= grindA x i t*(K x:ℂ)* tooth x i ^k
private lemma reed_driven (x: Tailor 1)(K:Tailor 1→ℝ)(k:ℕ)(v:ℝ): HasDerivAt (reed i K k x) (reed i K (k+1) x v) v := by
   have he t: grindA x i t=Complex.exp ((t:ℂ)*tooth x i):= by
      unfold grindA tooth mode; congr 1; calc
        _ = Complex.I*((axes (t • Pi.single i 1)) i * (x i:ℂ)) := by congr 1; rw [Finset.sum_eq_single i]; intro b _ hn; simp [axes, Pi.single_eq_of_ne hn]; simp
        _ = _:= by simp [axes]; ring
   simp_rw [reed,he]; have hu : HasDerivAt (fun s : ℝ => (s:ℂ)) 1 v := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
   convert ((hu.mul_const (tooth x i)).cexp.mul_const ((K x):ℂ)).mul_const (tooth x i^k) using 1 <;> first| rfl | (funext t; simp [reed,he])| ring
lemma reed_book {F: Field (Fin 2) (Node α)} (h:Pulse.Rooted (bath s 2 α) F b)(a: Fin 2→α) (k:ℕ)(hk:k≤2) (v:ℝ) : SumBudget (fun x:Tailor 1=> ‖reed i (extract F a) k x v‖) b:= by
   let f:=extract F a; have hp (x:Tailor 1): (Laurent.size x:ℝ)=Laurent.size (legLane x 1):= by unfold Laurent.size legLane; rw [Fintype.sum_prod_type, Fin.sum_univ_one]; rfl
   let X (z:Tailor 1):Locked (Node α) (0:Fin 2) (0,a 0):= ⟨publish 0 a z,by simp [publish,legLane]⟩
   have ht : Injective X:= fun x y h=> by simpa only [X,deg_issue] using (congr_arg (fun q : Locked (Node α) (0:Fin 2) (0,a 0)=> Spine.degree q.val) h)
   apply budget_mono (budget_pull _ ht (h.row 0 _)) (fun _=>norm_nonneg _) fun z=> ?_; simp [reed, grindA, tooth, mode_real _ _ (axes_real _),←Int.cast_abs, Int.natCast_natAbs (z i)] -- orientation
   let p :Tailor 1:= z; rw [← Int.natCast_natAbs]; let a₀:=X z; push_cast; change ‖(F a₀.val)‖*(_^k) ≤ ‖(F a₀.val)‖*_; refine mul_le_mul_of_nonneg_left ((show _≤mist s 2 (size (legLane p 1)) from ?_).trans ?_) (norm_nonneg _); swap; · apply le_trans _ ((bath s 2 α).width a₀.val 0 1); simp [a₀,X,Range.step,bath,p,publish,legLane]; rfl
   refine le_trans (b:=(1+(size p:ℝ))^2) ?_ ?_; swap; · unfold mist; rw [←hp]; exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity))
   have hl := single_le_sum (f:=fun k=> (z k).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ i); apply le_trans (b:=(1+(size p:ℝ))^k) ?_ (pow_le_pow_right₀ (by simp) hk); gcongr; norm_cast; rw [← Int.natCast_natAbs]; change (z i).natAbs≤size p at hl; omega
private def quote (K:Tailor 1→ℝ) (i:Keys 1)(k: ℕ)(t:ℝ):= ∑' x, reed i K k x t
theorem peek {F: Field (Fin 2) (Node α)} (h:Pulse.Rooted (bath s 2 α) F b)(a: Fin 2→α) (k:ℕ)(hk:k<2) (v:ℝ) : HasDerivAt (quote (extract F a) i k) (quote (extract F a) i (k+1) v) v := by
   let f:= reed i (extract F a) k; let g:= reed i (extract F a) (k+1); let u x:= ‖g x v‖
   have he x t : ‖g x t‖=u x:= by simp [u,g,reed,grindA,mode_real _ _ (axes_real _)]
   exact hasDerivAt_tsum_of_isPreconnected (reed_book i h a (k+1) hk v).2.1 isOpen_univ isPreconnected_univ (fun x t _=> reed_driven i x _ k t) (fun x t _=>(he x t).le) (Set.mem_univ _) (reed_book i h a k hk.le v).2.1.of_norm (Set.mem_univ v)
end shift
variable (i: G.ColorIndex) {P V:Field (Fin 2) (Node (Dye G))}
def priam (i:G.ColorIndex): Fin 2→ Dye G:= fun _=>(coord 1,i)
private lemma road_singular (p:Axis): roads (Lattice.step p)=Pi.single ( (0:Fin 1),p) (1:ℝ):= by ext1 ⟨j,a⟩; fin_cases j; by_cases h:a=p <;> simp [roads, h,Pi.single_apply,ContinuousLinearEquiv.coe_coe] -- inspect
-- ∂² along single coordinate
lemma speedy_beam (h:Pulse.Rooted (bath s 2 _) P b)(hs:0<s) :
   salvia G i P = (quote (extract P (priam i)) (0,0) 2 0).re := by
     let p:= ((0: Fin 1),(0:Axis)); let v:Stationary.Track:= step (0:Axis); let T:= mask (G:=G) P; let u:= pressLens T ![i,i] 1 1; let q:= quote (extract P (priam i)) p
     have hi : AnalyticAt ℝ u 0:= priceL (shadow_face _ _ (h.weaken bath_terrace le_rfl) hs) ![i,i] 1 1
     have he k (hk:k<2) : deriv (q k)=q (k+1):= funext fun x=>(peek p h (priam i) k hk x).deriv
     have hh(t:ℝ): u (t • v)=q 0 t:= by
       simp only [u,pressLens,v,mask,T,map_smul,road_singular]
       let j:= (![i,i]:Fin 2→G.ColorIndex); have hp : (fun a:Fin 2=>( (![coord (1:Axis),coord (1:Axis)]: Fin 2→ TypeFace 1) a,j a))=priam i:=by ext a<;> fin_cases a<;>rfl
       erw [hp]; unfold Laurent.read q quote; apply tsum_congr; intro x; unfold reed; rw [pow_zero,mul_one]; rfl
     let L := (ContinuousLinearMap.id ℝ ℝ).smulRight v; have hy:= (wired (f:=u) L (by rw [map_zero]; exact hi) 2 (fun _:Fin 2=>1))
     have hE : speedy u 2 v= ((2:ℝ)⁻¹) • iteratedDeriv 2 (u ∘ L) 0:= by rw [iteratedDeriv_eq_iteratedFDeriv]; rw [hy,map_zero]; unfold speedy Tensor.diagonal Tensor.coeff; norm_num [L,Function.comp_def]
     unfold salvia alphaPay; change 2*(speedy u 2 v).re= _; rw [hE, show u ∘ L=q 0 from funext hh, iteratedDeriv_succ,iteratedDeriv_one, he 0 (by norm_num), he 1 (by norm_num)]; change 2*( ( (2:ℝ)⁻¹) • (quote _ _ _ _)).re= _; rw [Complex.smul_re]; ring
lemma cash_salvia (h:Pulse.Rooted (bath s 2 _) P b)(hs:0<s) : ‖salvia G i P‖ ≤ b:= by rw [speedy_beam i h hs]; unfold quote; have hp:= reed_book (0,(0:Axis)) h (priam i) 2 le_rfl 0; exact (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hp.2.1).trans hp.2.2)
-- reserve quotes scaled width PER-level
section
variable {X:Type}[Fintype X]
lemma fit_spare (s η:ℝ≥0)(n:ℕ)(h:η<s): ∃ K≥1,∀ D:Type,∀ (Z:Type) (_:Fintype Z),∀ (x:Z→Node D), (bath η n D).bill x ≤ K*(terrain s D).bill x:= by
  obtain ⟨K,hK,H⟩:=Quill.expPocket s η n (by exact_mod_cast h); refine ⟨max 1 K,le_max_left ..,fun D Z _ x=> ?_⟩; apply (bath η n D).wide _ (by have he:= (terrain s D).one_bill x; exact one_le_mul_of_one_le_of_one_le (le_max_left ..) he); intro i j; change Real.exp _ * _ ≤ _; rw [mul_comm (Real.exp _)]; exact (H _ (by positivity)).trans ((mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)).trans (mul_le_mul_of_nonneg_left ((terrain s D).width x i j) (le_max_of_le_left zero_le_one))) -- infer
lemma expand_fee {b:ℝ}{F:Field X (Node α)} (h:η<s)(hs:Pulse.Rooted (terrain s _) F b): Pulse.Rooted (bath η k _) F ((fit_spare s η k h).choose * b):= by
   let K:=(fit_spare s η k h).choose; obtain ⟨hK,H⟩:= (fit_spare s η k h).choose_spec; refine ⟨mul_nonneg (zero_le_one.trans hK) hs.cash,fun i x=> ?_⟩; refine budget_mono (budget_scale (zero_le_one.trans hK) (hs.row i x)) (fun _=> by positivity) (fun p=>?_); exact (mul_le_mul_of_nonneg_left (H _ X _ p.val) (norm_nonneg _)).trans_eq (mul_left_comm ..)
end
lemma salvia_sum (h: Pulse.Rooted (terrain s _) P b)(hv: Pulse.Rooted (terrain s _) V c)(hp:0<s): salvia G i (P+V)=salvia G i P+salvia G i V:= by
   let η:= s/2; have he:0<η:=by unfold η; positivity
   have ht:η<s:=div_lt_self hp (by norm_num)
   let σ: Keys 1:=(0,(0:Axis)); let v:=priam i; have hP:= expand_fee (k:=2) ht h; have hV:= expand_fee (k:=2) ht hv; let a:= extract P v; let b:=extract V v;
   have hx x: reed σ (extract (P+V) v) 2 x 0=reed σ a 2 x 0+reed σ b 2 x 0:= by simp only [reed,b,a,extract,Function.comp_apply,Pi.add_apply]; push_cast; ring
   simp_rw [speedy_beam i hP he, speedy_beam i hV he,speedy_beam i (hP.add hV) he]; unfold quote; change Complex.re (tsum (fun x=> reed (0,(0:Axis)) (extract _ v) 2 x 0))=_; change Complex.re (∑' x,reed σ (extract _ v) 2 x 0)=_; simp_rw [hx]; rw [ (reed_book σ hP v 2 le_rfl 0).2.1.of_norm.tsum_add (reed_book σ hV v 2 le_rfl 0).2.1.of_norm]; rfl
lemma salvia_scale (h: Pulse.Rooted (terrain s _) P b)(hp:0<s) (a:ℝ): salvia G i (a • P)=a*salvia G i P:= by
   let η:= s/2; have he:0<η:=by unfold η; positivity
   have ht:η<s:=div_lt_self hp (by norm_num)
   let σ: Keys 1:=(0,(0:Axis)); let v:=priam i; have hP:= expand_fee (k:=2) ht h; have hx x: reed σ (extract (a • P) v) 2 x 0=a • reed σ (extract P v) 2 x 0:= by simp [Complex.real_smul,reed,extract]; ring
   simp_rw [speedy_beam i hP he,speedy_beam i (hP.smul a) he]; unfold quote; change Complex.re (∑' x,reed σ (extract _ v) 2 x 0)=_; simp_rw [hx]; rw [tsum_const_smul'',Complex.smul_re]; rfl
lemma salvia_zero : salvia G i 0=0:= by simpa using salvia_scale i (Pulse.Rooted.tranquility (ι:=Fin 2) (E:=ℝ) (terrain 1 (Dye G))) (by norm_num) 0
lemma salvia_finite {X:Type}{u:X→Field (Fin 2) (Node (Dye G))}(F:Finset X){b:X→ℝ}(h:∀ i∈F,Pulse.Rooted (terrain s _) (u i) (b i))(he:0<s): salvia G i (∑ j∈F,u j)=∑ j∈F,salvia G i (u j):= by
   induction F using Finset.induction with | empty=> simp only [sum_empty]; exact salvia_zero i | insert a v hv ih=> let g:= fun j hj=> h j (mem_insert_of_mem hj); rw [sum_insert hv,sum_insert hv,salvia_sum i (h a (mem_insert_self ..)) (Pulse.Rooted.aggregate v g) he,ih g]
end
end YM.Contacts.Milling.Lumen

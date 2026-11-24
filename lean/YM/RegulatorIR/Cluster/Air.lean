import YM.RegulatorIR.Cluster.Ward
import YM.RegulatorIR.Cluster.Extend
import YM.RegulatorIR.Diagram.Linear

/-! Multiply a source by another source on the cover before restricting, then
pass through both the horizontal and tree gauge substitution. Requires bounds
only on the used orders. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Budget Budget.Packet Budget.Tuple Diagram Uniform Gradient Train Finset Filter Brief
open scoped BigOperators Topology ENNReal NNReal Classical
variable {X Y Z:Type}{a b r p e n:ℕ} {T U:Orders X}

-- A row of Γ is required to be bounded in both indices (nothing more for
-- this equality). Nonlinear budget paid separately.
def CostRow (Γ:Curve X Y)(p:ℕ): Prop:=∀ i≤p,∃ b:ℝ≥0∞,b≠⊤ ∧ ∀ x y,‖Γ x i y‖ₑ ≤ b
def Bill (T:Orders X)(p:ℕ):Prop:=∀ i ≤ p,∀ r,quota (T i r) 1≠⊤
lemma parent (T U:Orders X)(h:Bill T p)(hh:Bill U p): Bill (accord T U) p:=by intro e he r; apply packable; intro i hi; apply packable; intro j hj; rw [← mem_antidiagonal.mp hj]; simp only [pie]; have hu:= mem_antidiagonal.mp hi; exact presume _ _ (h _ (by omega) _) (hh _ (by omega) _)

lemma Track_cost (Γ:Curve X Y)(g:Fin r→ℕ)(c:Fin r→ℝ≥0∞)(H:∀ i x z, ‖Γ x (g i) z‖ₑ ≤ c i)(x:Tuple X r)(y:Tuple Y (r+charge g)): ‖tracked Γ g x y‖ₑ≤∏ i,c i:= by rw [tracked,Train.units]; exact prod_le_prod' fun i _=> H ..
lemma track_sums (Γ:Curve X Y)(g:Fin r→ℕ)(T:Packet X r)(h:quota T 1≠⊤)(A:CostRow Γ p)(hp:charge g≤p)(y:Tuple Y (r+charge g)): Summable (fun z=>T z*tracked Γ g z y):=by
 choose c hc H using fun i:Fin r=>A (g i) (le_trans (Finset.single_le_sum (fun j _=>Nat.zero_le (g j)) (Finset.mem_univ i)) hp)
 have hx (l:Finset (Fin r)): (∏ i∈l,c i)≠⊤:=by induction l using Finset.induction_on with
  | empty=>simp
  | insert i l hh ih=> rw [Finset.prod_insert hh]; exact ENNReal.mul_ne_top (hc i) ih
 apply quota_summable (w:=1) (fun _=>le_rfl) (ne_top_of_le_ne_top (ENNReal.mul_ne_top h (show (∏ i,c i)≠⊤ from hx _)) ?_)
 rw [quota_base, quota_base,← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun i=>by rw [enorm_mul]; exact mul_le_mul_right (Track_cost Γ g c H i y) _

def tent (r:ℕ) (s: Finset X) : Finset (Tuple X r) := Fintype.piFinset (fun _=>s)
lemma tent_wide (r:ℕ): Tendsto (tent (X:=X) r) atTop atTop:= by
 refine tendsto_atTop_atTop.mpr (fun b=>⟨b.biUnion (fun x=>univ.image x),fun p hp x hx=>?_⟩)
 exact Fintype.mem_piFinset.mpr fun i=>hp (mem_biUnion.mpr ⟨x,hx,mem_image_of_mem x (mem_univ _)⟩)
lemma Track_winds (Γ:Curve X Y)(f: Z↪Y)(g:Fin r→ℕ)(T:Packet X r)(h:quota T 1≠⊤)(A:CostRow Γ p)(hp:charge g≤p) : Tendsto (fun l: Finset X=>series (fun i:l=>fun j=>crop f (Γ i j)) g (crop (tile l) T)) atTop (𝓝 (crop f (series Γ g T))):=by
 apply tendsto_pi_nhds.mpr;intro x
 let y:=acrossT f x
 have hv (l : Finset X): series (fun i:l=>fun j=>crop f (Γ i j)) g (crop (tile l) T) x = ∑ z∈tent r l,T z* tracked Γ g z y:=by
   rw [series,tsum_fintype]
   refine sum_bij (fun a _=> acrossT (tile l) a) (fun a _=> Fintype.mem_piFinset.mpr (fun i=> (a i).property)) (fun _ _ _ _ h=>injectT (tile l) h) ?_ (fun _ _=>rfl)
   intro a ha; exact ⟨fun i=>⟨a i,Fintype.mem_piFinset.mp ha i⟩,mem_univ _,rfl⟩
 have hM := (track_sums Γ g T h A hp y).hasSum.comp (tent_wide (X:=X) r); convert hM using 1; ext1 l; exact hv l
 rfl

variable (f:Z↪Y)(Γ:Curve X Y)
def house (l:Finset X):Curve l Z:= fun i j=>crop f (Γ i j)
def measureT (l:Finset X)(T:Orders X):Orders l:= fun i r=> crop (tile l) (T i r)
lemma measure_price (l:Finset X)(T:Orders X)(h:Ranks a T): Ranks a (measureT l T):=fun k i he=> h k i (fun hv=> he (by rw [measureT,hv]; rfl))
lemma cut_view (l:Finset X)(T U:Orders X): measureT l (accord T U)=accord (measureT l T) (measureT l U):=by ext1 e; ext1 i; exact crop_orders (tile l) _ _ _ _
lemma crop_clock (T:Packet Y r): crop f (symmetry T)= symmetry (crop f T):=by ext z;change symmetry _ (acrossT f z)=symmetry _ z; rw [symmetry_at,symmetry_at]; rfl
lemma dusk (A: CostRow Γ p)(T:Packet X r)(h:quota T 1 ≠ ⊤)(i:ℕ)(hi:i≤p): Tendsto (fun l=>updateQ (house f Γ l) (crop (tile l) T) i) atTop (𝓝 (crop f (updateQ Γ T i))):=by
 unfold updateQ; rw [crop_sum]; apply tendsto_finsetSum; intro g h'
 have he:= (turns_iff ..).mp h'
 subst i; simp only [cut, ↓reduceDIte]
 rw [crop_clock];exact draws_sym (Track_winds Γ f g T h A hi)
lemma drew (A:CostRow Γ p)(h:Bill T p)(ha:e+n≤p) i k: Tendsto (fun l=>Gradient.drawn (house f Γ l) (measureT l T) e n i k) atTop (𝓝 (crop f (Gradient.drawn Γ T e n i k))):=by
 by_cases hf:i+n=k
 · subst k; simp only [Gradient.drawn]; exact dusk f Γ A (T e i) (h _ (by omega) _) n (by omega)
 simp_rw [Gradient.drawn, dif_neg hf]; exact tendsto_const_nhds
lemma tides (A:CostRow Γ p)(h:Bill T p)(he:e≤p): Tendsto (fun l=>shot (house f Γ l) (measureT l T) e r) atTop (𝓝 (crop f (shot Γ T e r))):=by
 unfold shot; simp_rw [crop_sum]; apply tendsto_finsetSum; intro i hi; apply tendsto_finsetSum; intro j _
 exact drew f Γ A h (le_trans (mem_antidiagonal.mp hi).le he) j _
lemma port (A:CostRow Γ p)(h:Bill T p)(hh:Bill U p)(ht:Ranks a T)(hu:Ranks b U)[Fintype Z](he:e≤p): crop f (shot Γ (accord T U) e r)= crop f (accord (shot Γ T) (shot Γ U) e r):=by
 have h₁:= tides (r:=r) f Γ A (parent T U h hh) he
 simp_rw [cut_view,fun l=> shot_finite (measure_price l T ht) (measure_price l U hu) (house f Γ l)] at h₁
 apply tendsto_nhds_unique h₁; rw [crop_orders]; unfold accord crisp
 apply tendsto_finsetSum;intro i hi;apply tendsto_finsetSum;intro j hj
 rw [← mem_antidiagonal.mp hj]; simp only [pie]; apply draws_sym; apply tendsto_pi_nhds.mpr; intro x
 have hp:=mem_antidiagonal.mp hi;exact (tendsto_pi_nhds.mp (tides f Γ A h (show i.1≤p by omega)) (cutLeft x)).mul (tendsto_pi_nhds.mp (tides f Γ A hh (show i.2≤p by omega)) (cutRight x))
lemma shot_product (A:CostRow Γ p)(h:Bill T p)(hh:Bill U p)(ht:Ranks a T)(hu:Ranks b U)(he:e≤p): shot Γ (accord T U) e=accord (shot Γ T) (shot Γ U) e:=by
 ext1 i;ext1 x;let q:=univ.image x
 exact congr_fun (port (r:=i) (tile q) Γ A h hh ht hu he) (fun j=>⟨x j,mem_image_of_mem x (mem_univ j)⟩)

lemma sub_shot (A:CostRow Γ p)(h:Bill T p)(hh:Bill U p)(he:e≤p): shot Γ (T-U) e=shot Γ T e-shot Γ U e:=by
 ext1 i; rw [Pi.sub_apply];unfold shot; rw [← sum_sub_distrib];apply Finset.sum_congr rfl; rintro ⟨v,n⟩ hj; rw [← sum_sub_distrib];apply Finset.sum_congr rfl; intro b hb; have ht:=mem_antidiagonal.mp hj
 unfold Gradient.drawn; split_ifs with hu
 · subst i; change updateQ Γ (T (v,n).1 b-U (v,n).1 b) _=updateQ Γ _ _-updateQ Γ _ _
   unfold updateQ; rw [← sum_sub_distrib];apply Finset.sum_congr rfl;intro g hg; unfold cut;split_ifs with hv
   · -- avoid depend
     change charge g=n at hv
     change v+n=e at ht
     subst n
     change symmetry (series Γ g (T v b-U v b))= symmetry (series Γ g (T v b))-symmetry (series Γ g (U v b))
     rw [← symmetry_sub]; apply congr_arg;ext1 x; rw [Pi.sub_apply,series,series,series,← (track_sums Γ g (T v b) (h _ (by omega) _) A (by omega) x).tsum_sub (track_sums Γ g (U v b) (hh _ (by omega) _) A (by omega) x)]
     apply tsum_congr; intro i; exact sub_mul ..
   simp
 simp
end YM.RegulatorIR.Cluster

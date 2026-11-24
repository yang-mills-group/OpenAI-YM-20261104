import YM.Contacts.Barrage.Plume
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
structure Oasis (G:Gauge) where
    T: MapPrices
    a: Levels G
    Q: ChartRatio G
    M: Horizon a
    funded : Mirage T a Q
    lamp : M.Suffices T
    simple : G.Simple
    oga : LocalRatio Q
namespace Oasis
variable (e: Oasis G)
abbrev J(i:ℕ):= e.a.clock.J i
abbrev L(i:ℕ):=e.a.S.block i
abbrev R(i:ℕ):= mainFlag e.a i
def Z(i:ℕ):= lush (e.a.clock.hatBeta i)
def ξ(i:ℕ): ℝ≥0:= narrow (e.a.clock.hatBeta i)
lemma ξ_pos (i):0<e.ξ i:= narrow_pos _
lemma ξ_one (i):e.ξ i≤1 := NNReal.coe_le_coe.mp (inv_le_one_of_one_le₀ (lush_one _))
lemma z_pos (i):0<e.Z i:= lush_pos _
lemma z_ge (i):1≤e.Z i:= lush_one _
lemma z_two (i):2≤e.Z i:= le_add_of_nonneg_right (le_max_left ..)
lemma funded_tend : Tendsto e.Z atTop atTop:= lush_matures.comp (show Tendsto e.a.clock.hatBeta atTop atTop from tendsto_atTop_add_const_left _ _ (e.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos e.simple)))
lemma harbor (i): (e.L i).val ≤ e.Z i:= (e.funded.owns i).length
lemma shallow (i): e.Z (i+1) ≤ 3/2 * e.Z i:= by
   let β:= e.a.clock.hatBeta; let f i:= Real.log (Real.log (β i)); have hv j: 2≤β j:= (e.funded.owns j).iron.1
   let y:= (e.L i).val; have hx : G.slopeConstant * Real.log y ≤ β i:= (e.funded.owns i).iron.2; have hy:β (i+1) ≤ (β i)^2:= by rw [show β (i+1)=β i + G.slopeConstant*Real.log y from by simp only [β,L,Calendar.hatBeta,y,Schedule.scale_succ,Levels.S]; ring]; nlinarith only [hx,hv i]
   have hm:=Real.log_le_log (zero_lt_two.trans_le (hv (i+1))) hy; have ht:= Real.log_le_log (Real.log_pos (one_lt_two.trans_le (hv (i+1)))) hm; rw [Real.log_pow,Real.log_mul (by norm_num) ((Real.log_pos (one_lt_two.trans_le (hv i))).ne')] at ht; push_cast at ht
   suffices he : max 0 (f (i+1)) ≤ 1+max 0 (f i) by change 2+_≤ _*(2+_); change 2+max 0 (f (i+1)) ≤ _*(2+max 0 (f i)); linarith only [he, le_max_left 0 (f i)]
   apply max_le; · linarith only [le_max_left 0 (f i)]
   change f _ ≤ Real.log 2 + f _ at ht; exact ht.trans (add_le_add (by linarith only [Real.log_le_sub_one_of_pos zero_lt_two]) (le_max_right ..))
lemma lean_in (i): (2*(e.ξ i:ℝ))/(e.L i).val ≤ e.ξ (i+1) := by
   let l:ℝ:=(e.L i).val; have hx : 3 ≤ l:= (by unfold l; exact_mod_cast e.a.S.block_large i); have he : 0 < l:= lt_of_lt_of_le (by norm_num) hx; change _* (e.Z i)⁻¹ / l ≤ (e.Z (i+1))⁻¹; rw [← div_eq_mul_inv]; have hZ:= e.z_pos i; have hZ':= e.z_pos (i+1); field_simp; nlinarith only [e.shallow i,e.z_ge i,hx]
lemma leaving : Tendsto (fun i=>(e.L i).val) atTop atTop:= tendsto_atTop_mono (f:= e.J) (fun i=> (e.a.fits.mono (a:=i) (Nat.le_succ i) |>.trans ((Nat.le_add_left ..).trans (e.funded.funds i)))) e.a.fits.deep
lemma deep_lean (d:ℝ): ∀ᶠ i in atTop, d * (e.ξ i:ℝ) / (e.L i).val ≤ e.ξ (i+1):= by
   refine ((tendsto_natCast_atTop_atTop.comp e.leaving).eventually_ge_atTop (d*2)).mono fun i hi=> ?_; let l:ℝ:=(e.L i).val; have he:0 < l:= side_pos _; change d*(e.Z i)⁻¹ / l ≤ (e.Z (i+1))⁻¹; by_cases hp:0 ≤ d; swap; · exact le_trans (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (inv_nonneg.mpr <| (e.z_pos _).le)) he.le) (inv_nonneg.mpr (e.z_pos _).le)
   have ht:= mul_le_mul_of_nonneg_left (e.shallow i) hp; change d*2 ≤ l at hi; have hh:=mul_le_mul_of_nonneg_right hi (e.z_pos i).le; have hz:=mul_nonneg hp (e.z_pos i).le; rw [← div_eq_mul_inv]; have hZ:= e.z_pos i; have hZ':= e.z_pos (i+1); field_simp; nlinarith only [ht, hh, hz]
-- adj earnings
abbrev turn (i:ℕ):ℝ:= Real.exp ((Real.log (e.L i).val)/4)
abbrev drift (i:ℕ):= (e.turn i)⁻¹
def η (i N:ℕ):ℝ:= Real.exp (-(e.a.S.scale N - e.a.S.scale i)/4)
lemma η_pos (i N:ℕ): 0< e.η i N:= Real.exp_pos _
lemma drift_pos (i:ℕ): 0 < e.drift i:= inv_pos.mpr (Real.exp_pos _)
lemma turn_ge (i:ℕ): 1 ≤ e.turn i:= Real.one_le_exp (div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤(e.L i).val from (e.L i).property))) (by norm_num))
lemma turn_tend : Tendsto e.turn atTop atTop :=Real.tendsto_exp_atTop.comp ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp e.leaving)).atTop_div_const (by norm_num : (0:ℝ)<4))
lemma η_spin (i N:ℕ): e.η (i+1) N= e.turn i * e.η i N:= by unfold η turn; rw [Schedule.scale_succ,←Real.exp_add]; congr 1; ring
lemma turn_bound (i:ℕ): e.turn i ≤ e.Z i:= by
   refine le_trans ?_ (e.harbor i); unfold turn; calc
    _≤ Real.exp (Real.log (e.L i).val):=Real.exp_le_exp.mpr (div_le_self (Real.log_nonneg (by exact_mod_cast (show 1 ≤(e.L i).val from (e.L i).property))) (by norm_num))
    _ = _:= Real.exp_log (side_pos _)
lemma turn_contract (i:ℕ): Real.exp (-(Real.log (e.L i).val)/2)= (e.drift i)^2:= by unfold drift turn; rw [← Real.exp_neg,← Real.exp_nat_mul]; congr 1; push_cast; ring
@[simp] lemma self_η (i:ℕ):e.η i i=1:= by simp [η]
variable {P Q : ℕ→ ℝ→Prop}{p q:ℕ→ℝ}
structure Fair (f:ℕ→ℝ): Prop where
   bank i : 0 ≤ f i
   filled : ∃ k:ℕ,∀ᶠ i in atTop,f i ≤ e.Z i^k
def Permit (e: Oasis G)(P:ℕ→ ℝ→Prop):Prop:= ∃ p:ℕ→ℝ,e.Fair p ∧ ∀ i,P i (p i)
lemma fair_z : e.Fair e.Z := ⟨fun i=> (e.z_pos _).le, ⟨1,by simp⟩⟩
lemma fair_const (C:ℝ)(h:0≤C): e.Fair (fun _=> C):= ⟨fun _=> h, ⟨1,by simpa using e.funded_tend.eventually_ge_atTop C⟩⟩
namespace Fair
variable {e}
lemma admits (hp:e.Fair p)(h:∀ i,0 ≤ q i)(hh:∀ᶠ i in atTop,q i ≤ p i): e.Fair q:= by obtain ⟨k,hk⟩:=hp.filled; exact ⟨h,k,(hh.and hk).mono fun i ht=> ht.1.trans ht.2⟩
lemma congr (hp : e.Fair p)(h:∀ i,p i=q i) : e.Fair q:= funext h ▸ hp
lemma mul (hp:e.Fair p)(hq:e.Fair q): e.Fair (fun i=>p i*q i):= by
   obtain ⟨k,hk⟩:= hp.filled; obtain ⟨l,hl⟩:= hq.filled; refine ⟨fun i=>mul_nonneg (hp.bank i) (hq.bank i),k+l,(hk.and hl).mono fun i hi=>?_⟩; have hp:= pow_pos (e.z_pos i) k; rw [pow_add]; exact mul_le_mul hi.1 hi.2 (hq.bank i) hp.le
lemma add (hp:e.Fair p)(hq:e.Fair q): e.Fair (fun i=>p i+q i):= by
   obtain ⟨k,hk⟩:= hp.filled; obtain ⟨l,hl⟩:= hq.filled; refine ⟨fun i=> add_nonneg (hp.bank i) (hq.bank i),max k l+1,(hk.and hl).mono fun i hi=>?_⟩; rw [pow_succ]; let f:= e.Z i^max k l; have hh:0≤ f:= (pow_pos (e.z_pos i) _).le; have hl: p i ≤ f:= hi.1.trans (pow_le_pow_right₀ (e.z_ge _) (le_max_left ..)); have hn : q i≤f:= hi.2.trans (pow_le_pow_right₀ (e.z_ge _) (le_max_right ..)); change _≤f* _; nlinarith only [hl,hn,hh,e.z_two i]
lemma pow (hf:e.Fair p)(v:ℕ): e.Fair (fun i=>p i^v):= by induction v with|zero=>simp only [pow_zero]; apply e.fair_const 1 zero_le_one|succ i ih=>simp_rw [pow_succ]; exact ih.mul hf
lemma sum {β:Type}{f:β→ℕ→ℝ} (s:Finset β) (h:∀ i∈s,e.Fair (f i)):e.Fair (fun x=> ∑ i∈s,f i x):= by induction s using Finset.induction with| empty=> exact (e.fair_const 0 le_rfl).congr fun i=>by simp | insert i v hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih (fun i hi=>h i (mem_insert_of_mem hi)))
lemma next (hp:e.Fair p): e.Fair (fun i=>p (i+1)):= by
   obtain ⟨k,hk⟩:= hp.filled; have hx:= (e.fair_const ((3/2:ℝ)^k) (by positivity)).mul (e.fair_z.pow k);
   exact hx.admits (fun i=> hp.bank _) ((tendsto_atTop_mono (f:=id) (g:=fun x:ℕ=>x+1) Nat.le_succ tendsto_id).eventually hk|>.mono fun i hi => (show p (i+1) ≤ _ from hi).trans ((pow_le_pow_left₀ (e.z_pos _).le (e.shallow i) k).trans_eq (mul_pow ..)))
end Fair
lemma permit.exists (h:∀ i,∃ p,0≤p∧ P i p)(p:ℕ→ℝ)(he : ∀ᶠ i in atTop,P i (p i))(ht:e.Fair p): e.Permit P:= by
   let f i:= if H:P i (p i) then p i else (h i).choose; refine ⟨f,ht.admits (fun i=>?_) (he.mono fun i hi=> ?_), fun i=>?_⟩; · unfold f; split; apply ht.bank; exact (h i).choose_spec.1
   · unfold f; simp [hi]
   · unfold f; split; assumption; exact (h i).choose_spec.2
-- choose arbitrary gain, eventually enough to compress all powers by L^-some
private def plaster (g p f:ℕ→ℝ)(r i:ℕ):ℝ:= if _h:i < r then g i*plaster g p f r (i+1)+p i else f i
termination_by r-i
decreasing_by omega
lemma relax (g : ℕ→ℝ)(hg:Tendsto g atTop (𝓝 0))(hh:∀ i,0≤g i) (h:e.Fair p) : ∃ f:ℕ→ℝ,e.Fair f ∧ ∀ i,g i*f (i+1)+p i ≤ f i:= by
   obtain ⟨k,hk⟩:=h.filled; let f i:= 2*e.Z i^k; have hf:= (e.fair_const 2 zero_le_two).mul (e.fair_z.pow k); have hs: ∀ᶠ i in atTop,g i*f (i+1)+p i ≤ f i:= by
     refine (hk.and ((hg.mul_const (2 * ((3/2:ℝ)^k))).eventually_le_const (by simp : (0:ℝ)*_ <1))).mono fun i hi=> ?_; obtain ⟨ht,hi⟩:= hi
     have hz:=pow_le_pow_left₀ (e.z_pos _).le (e.shallow i) k; rw [mul_pow] at hz; change g i*(2*(3/2:ℝ)^k) ≤ 1 at hi; have he:= mul_le_mul_of_nonneg_right hi (pow_nonneg (e.z_pos i).le k); have hh:= mul_le_mul_of_nonneg_left hz (mul_nonneg (hh i) zero_le_two); unfold f; linarith (config := {splitHypotheses := true}) only [ht,hh,he] -- linarith monads normalize
   obtain ⟨r,hr⟩:= eventually_atTop.mp hs; let φ:= plaster g p f r
   have he (i:ℕ) : φ i=if i < r then g i*φ (i+1)+p i else f i:= by rw [show φ i=plaster g p f r i from rfl, plaster]; split <;> rfl
   have hR i (hi: r ≤ i): φ i=f i:= (he i).trans (if_neg (by omega))
   have ht i: 0 ≤ φ i:= by generalize hi:r-i=n; induction n using Nat.strongRecOn generalizing i with | _ n ih=> rw [he]; split; apply add_nonneg (mul_nonneg (hh i) (ih _ (by omega) _ (rfl : r - (i+1) =_))) (h.bank i); exact hf.bank i -- syntax
   exact ⟨φ,hf.admits ht ((eventually_ge_atTop r).mono fun i hi=>(hR i hi).le),fun i=> by rw [he i]; split; exact le_rfl; rw [hR _ (by omega)]; apply hr i (by omega) ⟩
lemma seal_gain {β:Type} (U:β→ℕ)(P:ℕ→β→ℝ→Prop) (H:∀ i y ⦃u v⦄,u≤v → P i y u → P i y v) (g:ℕ→ℝ)(hg:Tendsto g atTop (𝓝 0))(hh:∀ i,0≤g i)(h:e.Fair p) (hx:∀ y,P (U y) y (p (U y)))(hy:∀ i y,i<U y→ ∀ b,0≤b → P (i+1) y b→ P i y (g i*b+p i)) : e.Permit (fun i c=>∀ y,i ≤ U y → P i y c):= by
   obtain ⟨f,hf,hv⟩:= e.relax g hg hh h; refine ⟨f,hf,fun i y hi=>?_⟩; induction hi using Nat.decreasingInduction with
   | self =>exact H _ y (le_trans (le_add_of_nonneg_left (mul_nonneg (hh _) (hf.bank _))) (hv _)) (hx y)
   | of_succ i ht ih=> exact H i y (hv i) (hy i y ht _ (hf.bank _) ih)
end Oasis
end Reserve
end
end YM.Contacts.Barrage

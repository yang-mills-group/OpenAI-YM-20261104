import YM.OPE.Compatible.Lake.Lope
/-! Keep terminal subfilters open and price exact calibrated directions. Matrices extracted at every k (simultaneously). No limit commuted with one of the k clock.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories
open Next.Rank Next.Rank.Price
open scoped Topology Classical BigOperators
variable {d k N:ℕ} {G:Gauge}{C:Family G}(T:C.Makes)
set_option quotPrecheck false
local notation "F" => C.label d
local notation "L" => C.labels.level d
include T
def tallyman (d k:ℕ)(i:ℕ×ℕ) : C.label d →L[ℂ] C.label d:=
    if h:C.ref d≤k ∧ k ≤ i.1 then LinearMap.toContinuousLinearMap
       (((OPE.Columns.linTrace (p:=i.2) T h.1 h.2).mk' _).comp (C.factory d i.1 i.2).terminal.symm.toLinearMap) else 0
variable {p:ℕ}
lemma tallyCurrent (x:F) (he:C.ref d≤k)(hn:k≤N): tallyman T d k (N,p) x=Price.columns C d k N p x:=by rw [tallyman,dif_pos ⟨he,hn⟩]; rfl
omit T in
abbrev chargeTerm (D:ℕ)(v:C.label D) (u:C.label D ≃L[ℂ] C.label D):= (C.labels.level D).coeffSize (u v) -- k? remove
lemma capacity (he:C.ref d ≤ k)(hN:k≤N)(x:F): (L).coeffSize (tallyman T d k (N,p) x) ≤ OPE.Columns.juice C.path.levels k * (L).coeffSize x:= by
   induction k,he using Nat.le_induction with
   | base=>
      rw [tallyCurrent T x le_rfl hN]; change (L).coeffSize (((C.factory d N p).entries _ _).x) ≤ _
      rw [C.normalized T hN x]; exact le_mul_of_one_le_left (Work.G08.size_nonneg ..) (OPE.Columns.juice_pos ..)
   | succ j hj ih=>
     have hv : C.ref d ≤ j+1 := hj.trans (Nat.le_add_right j 1)
     have he: j ≤ N:= j.le_succ.trans hN; specialize ih he; rw [tallyCurrent T x hv hN]; rw [tallyCurrent T x hj he] at ih
     have hh := (T.calibrated d N p (hv.trans hN)).back j hj hN ((C.factory d N p).terminal.symm x)
     apply hh.trans ; apply (mul_le_mul_of_nonneg_left ih (zero_le_one.trans (C.path.levels.params (j+1)).columns_ge)).trans_eq
     rw [OPE.Columns.juice_step]; ring
structure Conic (φ : Filter (ℕ×ℕ))(Q:ℕ→ C.label d ≃L[ℂ] C.label d) : Prop where
    meeting i : C.ref d ≤ i → Tendsto (tallyman T d i) φ (𝓝 (Q i).toContinuousLinearMap)
variable {Q:ℕ→ C.label d ≃L[ℂ] C.label d}{φ:Filter (ℕ×ℕ)} [φ.NeBot]{H:Extraction.Order}(M:Conic T φ Q)
include M
variable (h:φ ≤ H.fuse) (hk:C.ref d ≤ k)
include h hk
local notation "A₀" => OPE.Columns.juice C.path.levels k
lemma up_bound (v:C.label d) : chargeTerm d v (Q k) ≤ (A₀) * (L).coeffSize v:=by
   have hV:= M.meeting k hk
   apply le_of_tendsto (b:=(A₀)*(L).coeffSize v) ((Size.continuous (L)).continuousAt.tendsto.comp (arcing hV (tendsto_const_nhds (x:=v))))
   filter_upwards [((Push.RelayDifference.cutoff_grows H).eventually_ge_atTop k).filter_mono h] with j hj using capacity T hk hj v
lemma down_bound (v:C.label d) : (L).coeffSize v ≤ outward C d k * chargeTerm d v (Q k):=by
   apply ge_of_tendsto (((Size.continuous (L)).continuousAt.tendsto.comp (arcing (M.meeting k hk) (tendsto_const_nhds (x:=v)))).const_mul (outward C d k))
   filter_upwards [((Push.RelayDifference.cutoff_grows H).eventually_ge_atTop k).filter_mono h] with j hj; rcases j with ⟨N,p⟩; change (L).coeffSize v ≤ _*(L).coeffSize ((tallyman T d k (N,p)) v); rw [tallyCurrent T v hk hj]; exact at_current C T hk hj p v
omit [φ.NeBot] in
lemma tallyRange (u:ℕ×ℕ→ C.label d)(p:C.label d)(hp:Tendsto u φ (𝓝 p)): Tendsto (fun i=> Next.UVStress.quota C d k i.1 i.2 (u i)) φ (𝓝 (chargeTerm d p (Q k))):=by
   apply ((Size.continuous (L)).continuousAt.tendsto.comp (arcing (M.meeting k hk) hp)).congr'
   filter_upwards [((Push.RelayDifference.cutoff_grows H).eventually_ge_atTop k).filter_mono h] with j hj; rcases j with ⟨N,p⟩; change (L).coeffSize ((tallyman T d k (N,p)) _)=(L).coeffSize _; rw [tallyCurrent T _ hk hj]; rfl
omit M T h hk [φ.NeBot] in
lemma paidTerm (z:C.label d)(m i j):Spindle.paid C d m i j z*C.S.a m^d=Next.UVStress.quota C d m i j z:=by
   rw [Spindle.paid,Price.awake,Size.smul,norm_inv,norm_pow, Complex.norm_real, Real.norm_of_nonneg (C.S.a_pos _|>.le)]
   rw [mul_comm,← mul_assoc,mul_inv_cancel₀,one_mul] -- maybe one_mul
   · rfl
   exact pow_ne_zero _ (C.S.a_pos _).ne'
end YM.OPE.Lake

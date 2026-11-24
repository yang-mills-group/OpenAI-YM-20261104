import YM.FormalBulk08.Avenue.Kens
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries

section
variable (P:Flight j u)(R:Lodge P.patch) (K:KernelChoices)(n:Side)
def trMean (G:Gauge) := (dropRoot G (primary P.patch K n) (Reef.floor K P R n))ᵀ*pMean G K P n (Reef.floor K P R n)
lemma stirlev {I J:Type*} (f:Row I J)(x:Site n×I)(z:Site n×J) [Fintype I][Fintype J](h:f.strip η C)(hs:0≤η)(hc:0≤C): ‖f.acts n x z‖≤ (Fintype.card J)*C:= by
    have hx:=trundle n f h hc hs; have he:‖f.acts n x z‖ₑ ≤ ENNReal.ofReal _:= (le_mul_of_one_le_left' (shine_plus η hs _)).trans ((ENNReal.le_tsum (f:=fun v=> Lotus.rinkshine η n x v*‖f.acts n x v‖ₑ) z).trans (hx.rows _)); rw [←ofReal_norm] at he; exact (ENNReal.ofReal_le_ofReal_iff hx.costs).mp he
lemma fine_fee (G:Gauge)(hi:4≤u):∃ C:ℝ,0≤ C∧ ∀ n i j, ‖trMean P R K n G i j‖ ≤ C:= by
    obtain ⟨σ,A,hσ,hA,H⟩:=Bank.aone P (K:=K) G hi; obtain ⟨C,hc,T⟩:=Lodge.bothPay G K R σ hσ; obtain ⟨hr,-,ht⟩:=T _ A hA H
    let V:= locating G K P R; let F(n:Side):=Reef.floor K P R n; let Y n:=pMean G K P n (F n);
    refine ⟨(Fintype.card (Loc G 1):ℝ)*(C*A),by positivity,fun n i j=> ?_⟩
    have he v b: ‖Y n v b‖ ≤ (Fintype.card (Loc G 1):ℝ)*(C*A):= by
       let E:= R.splitting (S:=primary P.patch K n) (G:=G);have ha:= (ht n).1; change V.acts n=repackM E (Equiv.refl _) (Y n) at ha
       have hh : Row.strip V σ (C*A):=hr; have hv := stirlev n V (E v) b hh hσ.le (mul_nonneg hc.le hA); rw [ha] at hv;simpa only [repackM,Matrix.reindex_apply, Matrix.submatrix_apply,Equiv.symm_apply_apply, Equiv.refl_symm,Equiv.refl_apply] using hv
    let q:=dropRoot G (primary P.patch K n) (F n)
    have hh : trMean P R K n G i j=(qᵀ*ᵥ Matrix.col (Y n) j) i:= by unfold trMean;simp [Matrix.col,Matrix.mul_apply,Matrix.mulVec,dotProduct,q,Y,F]
    rw [hh]; by_cases hv: lives (S:=primary P.patch K n) (F n) i; rw [show (qᵀ *ᵥ _) _= _ from bring_alive (F n) _ (G:=G) ⟨i,hv⟩]; exact he _ _
    rw [show (qᵀ *ᵥ _) _=0 from bring_dead (F n) _ hv,norm_zero]; positivity
end
lemma stare_walk (v:Train j)(k:ℝ)(x:Cover)(T:Tile (edgeL G) (r+2)): stare (bandP G v k) (carries x T)=carries x (stare (bandP G v k) T):= by
   let L:= Lotus.tint (I:=Loc G 1) (-x)
   ext1 i; let V:=L ∘ i; change (∑' a,telescopeTerm _ _ _ a)=∑' a,telescopeTerm _ _ V a; rw [←Equiv.tsum_eq (Equiv.prodCongr L L) (fun a:(edgeL G × edgeL G)=>telescopeTerm (bandP G v k) T V a)]; apply tsum_congr; rintro ⟨a,b⟩; unfold telescopeTerm Lava.shed; simp only [Equiv.prodCongr_apply, Prod.map_apply]; rw [show bandP G v k (L a) (L b)=bandP G v k a b from ?_]; swap
   · simp [bandP,L, Lotus.tint]
   congr 1; unfold Kemp.carries jetty V; apply congr_arg T; ext1 u; rw [Fin.comp_cons,Fin.comp_cons]
lemma page_shift (v:Train j)(k:ℝ)(y:Cover)(P:Beams (edgeL G))(d:ℕ): pageant (bandP G v k) (fun i=>carries y (P i)) d r = carries y (pageant (bandP G v k) P d r):= by
    have he d r : bleat (bandP G v k) (fun i=>carries y (P i)) d r=carries y (bleat (bandP G v k) P d r):= by
       induction d generalizing r with
       | zero=>rfl
       | succ i ih=>rw [bleat]; dsimp only; rw [ih,stare_walk]; rfl
    unfold pageant; simp_rw [he]; funext i; unfold Kemp.carries jetty; simp_rw [Finset.sum_apply]; rfl
lemma kinkwind (v:Train j)(k:ℝ)(hk:0<k)(hj:4≤j)(p:Studio D){T:Anthem D G}(h:Wade x T l)(z:Cover)(r:ℕ):∃ η:ℝ,0<η ∧ Kalm η (z,x) (carries z (winner v k l T p r)) (fun n=>marble r (binned v k n (Kemp.banner l (work z (T p)) n))):= by
    obtain ⟨η,hv,H⟩:=sunny T x h; let V:= work z (T p); have he: Young V l:= by
        intro e r he; apply h.1; intro hv;apply he; unfold V work; rw [hv]; rfl
    have hp n r: marble r (coeff 0 (Kemp.banner l V n))= sieve n (V 0 r):= badge V he (fun _ _ u v=> carrying _ v (h.2.1 _ _ _) u) le_rfl n 0 r
    refine ⟨η,hv,?_⟩; rw [winner,←page_shift]; refine kain v hk hj (V 0) _ (fun r=> ?_) (fun n r ht=>?_) hv r
    · change Kalm _ _ _ (fun n=> marble r (coeff 0 (Kemp.banner l V n))); simp_rw [hp _ r]
      obtain ⟨C,hc,hX⟩:= H r; have hu:= mantle_pay z (hX p); rw [show tint z (show edgeL G from (0,x))=(z,x) from Prod.ext (zero_add _) rfl] at hu; exact sieve_kalm _ hu hv.le
    rw [hp n r, show V 0 r=0 from Classical.byContradiction (fun hx=> (not_lt.mpr (he _ _ hx)) ht),sieve_zero]
end YM.FormalBulk08.Avenue

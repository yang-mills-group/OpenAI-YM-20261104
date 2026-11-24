import YM.FormalOPE.RG10.Carryon.Flash
/-!
# Credit for finite position operations. It isn't licit to assume regulators yielding all
orders even at one test; we lift a strictly finite Taylor supply. Uses accepted analytic
branch- and algebra-continuity (going via auxiliary artificially completed jets to use those APIs).
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G : Gauge} {F : Frames G} {d : ℕ}
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
variable {Y:Drivers}
-- filler with **given full-at-limit**, while the family approaches only through the
-- target order
variable (r:ℕ)
def up (p q: fps) : fps:=PowerSeries.mk fun j=> if j≤r then coeff j p else coeff j q
lemma copy (p q: fps) : Through r (up r p q) p:= by intro i hi; simp [up,hi]
lemma aligning {α:Type*}{l:Filter α}{u:α→fps}{p:fps}(h:∀ i∈range (r+1), Tendsto (fun x=>coeff i (u x)) l (𝓝 (coeff i p))) : AlignSeries l (fun i=> up r (u i) p) p:= by
 intro i; by_cases hi:i≤r
 · simpa only [up,coeff_mk, if_pos hi] using! h i (by simp [hi])
 simp only [up,coeff_mk,if_neg hi]; exact tendsto_const_nhds
lemma returning {p:ℕ+→ℕ→Warp}{q:Warp}(h:Y.Credit (fun i j=>(p i j).x) q.x)(hQ:q.Hot): Y.Credit (fun i j=> (p i j).refund.x) q.refund.x:= by
 intro k; unfold Drivers.Harvest; filter_upwards [eventually_all_finset (range (k+1)) |>.mpr (show ∀ j∈range (k+1), Y.Harvest _ (coeff j q.x) from fun j _=> h j)] with i hv
 let y(j:ℕ):=(p i j); let x(j:ℕ): Warp:= ⟨_, ((coeff_zero_eq_constantCoeff_apply (up k (y j).x q.x)).symm.trans ((copy k (y j).x q.x _ (Nat.zero_le _)).trans ((coeff_zero_eq_constantCoeff_apply _).trans (y j).atOrigin)))⟩
 have hl:= aligning k (p:=q.x) (u:=fun j=> (y j).x) hv
 apply (hl.inverse_est (isUnit_iff_ne_zero.mpr hQ) k).congr; intro j; exact Warp.either (p:=x j) (q:=y j) (copy _ _ _) k le_rfl
lemma crossing {p:ℕ+→ℕ→Warp}{q:Warp}(h:Y.Credit (fun i j=>(p i j).x) q.x){f:ℕ+→ℕ→fps}{g:fps}(hg:Y.Credit f g): Y.Credit (fun i j=> (p i j).charge (f i j)) (q.charge g):= by
 intro k;
 -- sum! choose all finite k only
 unfold Drivers.Harvest
 filter_upwards [eventually_all_finset (range (k+1)) |>.mpr (show ∀ j∈range (k+1), Y.Harvest _ (coeff j q.x) from fun j _=> h j), eventually_all_finset (range (k+1)) |>.mpr (show ∀ j∈range (k+1), Y.Harvest _ (coeff j g) from fun j _=> hg j)] with i hv hz
 let y(j:ℕ):=(p i j); let x(j:ℕ):Warp:= ⟨_, ((coeff_zero_eq_constantCoeff_apply (up k (y j).x q.x)).symm.trans ((copy k (y j).x q.x _ (Nat.zero_le _)).trans ((coeff_zero_eq_constantCoeff_apply _).trans (y j).atOrigin)))⟩
 have hx: AlignSeries atTop (fun j=> (x j).x) q.x:= aligning k (p:=q.x) (u:=fun j=>(p i j).x) hv
 have he := (hx.compose (aligning k hz) q.atOrigin (Eventually.of_forall fun j=> (x j).atOrigin)) k
 rw [Warp.turning]; apply he.congr
 intro j; change coeff k (subst (x j).x _) = _; rw [← Warp.turning]; exact Warp.charges (p:=x j) (q:=p i j) (copy _ _ _) (copy k (y j).x _) k le_rfl

section Pose
variable {D:Stock F}{p:Mark (Deck F d) PertExtension.Physical.Profile.n →fps}
  {u:ℕ+→ℕ→Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
local notation "a"=> PertExtension.Physical.Profile.n
lemma lighten (h: Official D)(hp:∀ i,constantCoeff (p i)= raw F d i)
    (he:∀ j,Y.Credit (fun q k=>u q k j) (p j)) (j:V d): Y.Credit (fun q k=>post D (u q k) j) ((D d).positioned p j):= by
 intro k
 let E:= D d; let s := Insert.insert j.1 E.tests;
 let Dg t m (i:V d):= if i.1∈s then up k (u t m i) (p i) else p i
 let p0:= fun i=> constantCoeff (p i)
 have hB : p0=raw F d := funext hp
 have hz : E.Regular p0:= hB ▸ h.fresh d
 have hw (m:ℕ+) (i:ℕ) : Through k (post D (Dg m i) j) (post D (u m i) j):= by
   have ha : ∀ r∈s,Sync k (Dg m i) (u m i) r:= by
     intro r hr v; unfold Dg; simp_rw [if_pos (show (⟨r,v⟩:V d).1∈s from hr)]; exact copy _ _ _
   exact posting (fun r h=> ha _ (mem_insert_of_mem h)) _ (ha _ (mem_insert_self ..)) j.2
 unfold Drivers.Harvest; let w:= markIn (J:=Deck F d) (arity:=a) s
 filter_upwards [eventually_all.mpr (show ∀ x,∀ᶠ v in Y.ages, ∀ n∈range (k+1), Tendsto (fun i=> coeff n (u v i (w x))) atTop (𝓝 (coeff n (p (w x)))) from fun x=> eventually_all_finset _ |>.mpr (fun n _=> he (w x) n))] with i hi
 have ha : ∀ j : V d,AlignSeries atTop (fun v=> Dg i v j) (p j):= by
   intro x; by_cases hk : x.1∈s
   · simp_rw [Dg,if_pos hk]; apply aligning; exact hi ⟨⟨x.1,hk⟩,x.2⟩
   simp_rw [Dg,if_neg hk]; exact AlignSeries.const _
 have hd l: E.systemAt p (Dg i) l = crib D (Dg i l):= by unfold TestSystem.systemAt; congr
 apply (E.positions_align p (Dg i) hz ha j k).congr; intro m; change coeff k ((E.systemAt p (Dg i) m).positioned _ j) = _; rw [hd]; exact hw _ _ _ le_rfl
end Pose
end YM.FormalOPE.RG10.Carryon

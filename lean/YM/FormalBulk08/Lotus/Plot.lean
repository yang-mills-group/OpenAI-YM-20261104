import YM.FormalBulk08.Lotus.Barge

/-! Winding limit for single steps (never iterate this estimate). We switch
the alphabet for each torus to an origin representation. Dominated convergence
through this moving chart. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} {η C : ℝ} {r : ℕ}

structure Jolt (V : Type*) (H : Side→Type*) where
    give (n : Side) : V→ H n
    undo (n : Side) : H n → V
    back : ∀ n x, give n (undo n x)=x
    tame : ∀ x,∀ᶠ n in atTop, undo n (give n x)=x
lemma jolt_limit {V : Type*} {H : Side →Type*} (k : Jolt V H) (T : (n:Side)→ H n →ℝ) (F : V →ℝ)
    (U : V→ℝ) (hu : Summable U) (hn : ∀ i, 0≤U i) (he : ∀ x,Tendsto (fun n=> T n (k.give n x)) atTop (𝓝 (F x)))
    (hy : ∀ᶠ n in atTop, ∀ x, ‖T n x‖≤ U (k.undo n x)) : Tendsto (fun n=> ∑' j, T n j) atTop (𝓝 (∑' x, F x)) := by
   let A n (x:V):=if k.undo n (k.give n x)=x then T n (k.give n x) else 0
   have hx n : (∑' j,T n j) = ∑' x,A n x := by
      have h : ∑' j,A n (k.undo n j)=∑' x,A n x:= by
         apply Function.Injective.tsum_eq (show Injective (k.undo n) from fun a b e=> (k.back n a).symm.trans ((congr_arg (k.give n) e).trans (k.back n b)))
         intro x hh; change A n x≠0 at hh; unfold A at hh;split_ifs at hh with h'
         · exact ⟨_,h'⟩
         contradiction
      rw [←h]; exact tsum_congr fun j=>by simp [A,k.back]
   simp_rw [hx]; apply tendsto_tsum_of_dominated_convergence hu (fun x=>(he x).congr' ((k.tame x).mono (fun n e=> by simp_rw [A, if_pos e])))
   filter_upwards [hy] with n h x; unfold A;split_ifs with ha
   · have hb:= h (k.give n x); rw [ha] at hb; exact hb
   simpa using hn x

def glide (I : Type*) : Jolt (Biglot I) (fun n=>Tor n I) := ⟨fun n=>drip n, fun n=> boil n,drip_boil,boil_drip⟩
def glaze (I : Type*) (r : ℕ) : Jolt (chain (Biglot I) r) (fun n=>chain (Tor n I) r) :=
    ⟨fun n v=> drip n ∘ v,fun n w=> boil n ∘ w,fun n _=> funext fun _=>drip_boil n _,fun v=> (eventually_all.mpr (fun i : Fin r=>boil_drip (v i))).mono fun _ he=> funext fun i=> he i⟩
def windup (I J : Type*) : Jolt (Biglot I × Biglot J) (fun n=>Tor n I × Tor n J):=
    ⟨fun n=>Prod.map (drip n) (drip n),fun n=>Prod.map (boil n) (boil n),fun _ _=> Prod.ext (drip_boil ..) (drip_boil ..),fun v=>((boil_drip v.1).and (boil_drip v.2)).mono fun _ he=> Prod.ext he.1 he.2⟩

def Light (T : Tile (Biglot I) r) (F : (n:Side)→ Tile (Tor n I) r) := ∀ v,Tendsto (fun n=>F n (drip n ∘ v)) atTop (𝓝 (T v))
def Bright (F : (n:Side)→Tile (Tor n I) r) (η C : ℝ) := ∀ᶠ n in atTop, Bail (lake n I) η (F n) C
lemma spark (T : Tile (Biglot I) r) (i : Fin r) {s C : ℝ} (hs : 0≤s) (H : Bail (fame I) s T C) (h : Up T) :
    Light T (fun n=>cum i n T) := by
   intro v; let w n := drip n ∘ v
   let U n : Set (pack i (v i)) := {u| drip n ∘ u.val=w n}
   let f n := (U n).indicator (fun u=>T u.val)
   have e n : cum i n T (w n) = ∑' u,f n u := by
      rw [cum_near _ _ h (w n) (v i) rfl]; unfold vat f;rw [←tsum_subtype]
      let t : Picks i n (v i) (w n) ≃ U n:= ⟨fun x=>⟨⟨x.val,x.property.1⟩,x.property.2⟩,fun y=> ⟨y.val.val,y.val.property,y.property⟩,fun x=>rfl,fun y=>rfl⟩
      exact Equiv.tsum_eq t (fun x=> T x.val.val)
   change Tendsto (fun n=>cum i n T (w n)) _ _; simp_rw [e]
   let y (u : pack i (v i)) := if u.val=v then T u.val else 0
   have hh : (∑' u,y u)=T v:= by rw [tsum_eq_single (⟨v,rfl⟩ : pack i (v i)) (fun u hu=>if_neg (fun he=> hu (Subtype.ext he)))]; simp
   conv_rhs => rw [←hh];
   have he := (H.shrink hs).measured i (v i); simp only [zero_mul,Real.exp_zero,one_mul] at he
   refine tendsto_tsum_of_dominated_convergence he.1 (fun x=>tendsto_const_nhds.congr' ?_) (.of_forall fun n u=> ?_)
   · by_cases hy : x.val=v
     · exact .of_forall fun n=>by dsimp only; unfold f; rw [indicator_of_mem (show x∈ U n by change drip n ∘ x.val= drip n ∘ v; rw [hy])];simp [y,hy]
     obtain ⟨j,hj⟩:=Function.ne_iff.mp hy
     filter_upwards [same_drip (x.val j) (v j)] with n hn; unfold y f; rw [if_neg hy,indicator_of_notMem]; exact fun hz=> hj (hn.mp (congr_fun hz j))
   by_cases hu : u∈U n
   · unfold f; rw [indicator_of_mem hu]
   unfold f; rw [indicator_of_notMem hu,norm_zero]; exact norm_nonneg _
end YM.FormalBulk08.Lotus

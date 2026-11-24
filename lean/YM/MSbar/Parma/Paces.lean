import YM.MSbar.Parma.Boats
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}(g:Ratio c n)(P:Cross g.count (TypeFace 1) (TypeFace 1))
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "ℓ"=>Measuring.chart n G
local notation "T"=>Measuring.chart c G
local notation "R"=>installed g P
open MvPolynomial
lemma levy (x:Positions (Primary c G))(p:Pot (Primary n G)):clue (Rolling.rail (maple (installed g P) G) p) x=clue p (Lis.roll g P G x):=by
    have hp:maple (installed g P) G= pension g P G []:=by ext x y; simp only [maple,pension, of_apply,advanceC]; simp [eq_comm]
    rw [hp]; exact congr_fun (clearL ..) p
-- embed.LinearMech
noncomputable def spent(a:ℝ) := a/g.count.val
variable {a b E D V Φ Z φ ν η:ℝ}{p q m k r:ℕ}
lemma dilate(t:List (Primary c G)) (hp:0≤a) : swipe (Measuring.chart c G) a m t ≤ swipe (Tramp.path g G) (a/(g.count.val:ℝ)) m t:=by
    let W:= Whisk.zone T ∅ t; let F:=Tramp.path g G; let d:=extent W; let e:=extent (Whisk.zone F ∅ t); let L:=g.count.val; have hx:L*d≤e:=by
        by_cases h: W.Nonempty
        · obtain ⟨x,hx,hF⟩:= Finset.exists_mem_eq_sup W h (fun i=> W.sup (fun j=> separation i j)); obtain ⟨y,hy,hD⟩:= Finset.exists_mem_eq_sup W h (fun j=> separation x j); rw [show d=separation x y from hF.trans hD]; refine (Corona.below g x y).trans (Whisk.curve ?_ ?_)
          · obtain ⟨j,hj,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp (show x ∈ _ from (by simpa only [W,Whisk.zone,Finset.empty_union] using hx))); exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨j,hj,rfl⟩))
          obtain ⟨j,hj,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp (show y ∈ _ from (by simpa only [W,Whisk.zone,Finset.empty_union] using hy))); exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨j,hj,rfl⟩))
        rw [show d=0 from ?_]; simp
        unfold d extent; rw [Finset.not_nonempty_iff_eq_empty.mp h]; rfl
    have hL : L≥1 := g.count.property; change liftW a m d≤ liftW _ _ e; unfold liftW; apply mul_le_mul ?_ (Real.exp_monotone ?_) (Real.exp_pos _|>.le) (by positivity)
    · have h:d ≤ e:= (Nat.le_mul_of_pos_left _ hL).trans hx; gcongr
    have he:0 < (L:ℝ):=by exact_mod_cast hL
    apply le_trans (b:=a/(L:ℝ)*(L*d)) ?_ (mul_le_mul_of_nonneg_left (by exact_mod_cast hx) (div_nonneg hp he.le)); field_simp; rfl
lemma descendent (F:Pot (Primary c G))(hp: Tin (Tramp.path g G) (a/(g.count.val:ℝ)) p m V F Z)(ha:0≤a) : Tin (Measuring.chart c G) a p m V F Z:=by refine ⟨hp.1,fun k hk i=>?_⟩; rw [←scored]; refine le_trans ?_ ((scored F i).le.trans (hp.fan k hk i)); refine shiny k fun j _=> ?_; exact mul_le_mul_of_nonneg_left (dilate g _ ha) (abs_nonneg _) -- add args
lemma sunrise {σ:Type}[Fintype σ][DecidableEq σ](L:σ→Site c)(h:b≤a)(f:Cacao.Pot σ)(hp: Tin L a p m V f Z): Tin L b p m V f Z:=by
    refine ⟨hp.1,fun k hk i=>?_⟩; rw [← scored]; refine le_trans ?_ ((scored f i).le.trans (hp.fan k hk i)); refine shiny k fun j _=>?_ ; unfold swipe Whisk.spread liftW; gcongr
variable (h:Cane P D η a E k p)(hx:a/(g.count.val:ℝ) ≤ b)(hb:1≤ V) {f:Pot (Primary n G)}{k':ℝ}(hf:Tin (Measuring.chart n G) b p q V f k') -- placeholders
open Metric Set Cane
local notation "L"=>(g.count.val:ℝ)
local notation "σ"=>value a D η E p k
include h hx hb hf
lemma high (i:ℕ)(hi:i≤q) (j:Y) : cog T a p (Rolling.rail (maple R G) f) i j ≤ ((k'*L^4)*(σ/L)^(i+1))/V^(i+1):=by
    have hv:0<V:=zero_lt_one.trans_le hb
    have hp:JetTab ℓ b p V ({0}:Set (Positions (Primary n G))) (clue f) i k':= (CrossH.pressed _ _ _ _ _ _ _ hv).mpr ⟨hf.1,hf.2 _ hi⟩
    have hh:=waterfall g P (clue f) h hx hv hv hp (show Set.MapsTo (Lis.roll g P G) {0} {0} from (by simp [Set.MapsTo])) (fun x hx=>(helm f (i+1)).contDiffAt) le_rfl
    rw [← show clue ((Rolling.rail (maple R G)) f)=clue f ∘ (Lis.roll g P G) from funext (fun q=> levy g P q f)] at hh; rw [div_self hv.ne',one_pow,one_mul] at hh; exact (CrossH.pressed _ _ _ _ _ _ _ hv|>.mp hh).2 j
end YM.MSbar.Parma

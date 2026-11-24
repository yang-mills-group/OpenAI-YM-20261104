import YM.X.Tot.Presence
/-!
# Milestones of emission estimation: Ash progr (one extra UV power factor). local ideals.Audit.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {p:Word G}
variable (u:ℕ)(S:Bare.Shop F)(χ:Floor R)(hq:1<q.val)
local notation "ε"=>epsilon q
abbrev Ready (q:ℕ+)(T:Submodule ℝ (Fan G)):= Page q Set.univ (Set.univ (α:=Bone G T))
def epi (q:ℕ+)(a:ℤ)(k:ℕ) : ℂ:= ((epsilon q k)^a:ℝ)
def zoomA (q:ℕ+)(a:ℤ): Module.End ℂ (Foam G) where
    toFun f:= epi q a • f; map_add' _ _:= smul_add _ _ _; map_smul' c a:= smul_comm ..
lemma zoom_pose {a:ℤ}(v:Foam G): zoomA q a v=epi q a • v:= rfl
lemma zoom_slide (a b:ℤ)(f:Foam G):zoomA q a (zoomA q b f)=zoomA q (a+b) f:= by rw [zoom_pose,zoom_pose,zoom_pose, smul_smul]; apply congr_arg (· • f); funext k; rw [epi,zpow_add₀ (epsilon_pos q _).ne',Complex.ofReal_mul]; rfl
@[simp] lemma zoom_self (p:Foam G) : zoomA q 0 p=p:= by rw [zoom_pose, show epi q 0=1 from funext (fun i=>by simp [epi])]; exact one_smul (ℕ→ℂ) p
lemma zoom_back (f:Foam G): zoomA q 1 (zoomA q (-1) f)=f:= by rw [zoom_slide,add_neg_cancel,zoom_self]
lemma price_zoom (a b:ℤ)(f:Curly G):zoomA q a (priceCo q b f)= priceCo q (a+b) f:= zoom_slide .. -- definitionally point
variable {T:Submodule ℝ (Fan G)}
def Ash (q:ℕ+)(T:Submodule ℝ (Fan G)):Submodule ℂ (Foam G):= (Ready q T).comap (zoomA q (-1))
include hq
lemma ash_ready {f:Foam G}(h: f∈ Ash q T) : f∈ Ready q T:= by
   change zoomA q (-1) f∈ Ready q T at h; nth_rw 1 [← zoom_back (q:=q) f]; exact page_scale _ _ (fares_h q _ (by norm_num) hq) h
lemma ash_vertex {f:Curly G} (h:f ∈ verse T (u+1)): priceCo q (-(u:ℤ)) f∈ Ash q T:= by rw [Ash, Submodule.mem_comap,price_zoom,show (-1:ℤ)+(-(u:ℤ)) = -(↑(u+1):ℤ) from by omega]; exact verse_page q hq h
local notation "L"=> (Reed.Horizontal G)
lemma ash_leaf (p:Word G) : (fun i=> milk (qu q G i) (mint (ε i) p 0)) - priceCo q (-(p.d:ℤ)) (Grow.looking p)∈ Ash q L:= by
    change zoomA q (-1) _∈ Ready q L; let t : Foam G :=fun i=>load q p i-Grow.looking p; let n:= (-(p.d:ℤ)); have he (i): milk (qu q G i) (mint (ε i) p 0) -priceCo q n (Grow.looking p) i= epi q n i • t i:= by rw [mint, RCLike.real_smul_eq_coe_smul («K»:=ℂ),map_smul]; unfold epi priceCo t; rw [smul_sub];rfl
    rw [show (fun i=> milk (qu q G i) (mint (ε i) p 0)) -_= zoomA q n t from funext he,zoom_slide]; exact page_hor q (self_ration hq p) hq -- T type infer
lemma stan_h (p:Label G d): stance S q d p∈ Ready q L:= by
    rw [← (F.level d).basis.sum_repr p,map_sum]; apply Submodule.sum_mem; intro i _; rw [map_smul]; apply Submodule.smul_mem; let X:= stance S q d ((F.level d).basis i); let Y:= (useWord S i); rw [funext (fun k:ℕ=>stanza_name (q:=q) (k:=k) S i)]; -- note Y? parser
    exact (sub_add_cancel (fun k=> milk (flow G (side q k)) (mint (ε k) Y 0)) (priceCo q (-(Y.d:ℤ)) (Grow.looking Y))) ▸ Submodule.add_mem _ (ash_ready hq (ash_leaf hq Y)) (verse_page q hq (press_word Y))
def priceL (q:ℕ+)(a:ℤ) : Curly G→ₗ[ℂ] Foam G where
   toFun := priceCo q a; map_add' v x:= funext fun i=> smul_add _ _ _; map_smul' c p:= funext (fun x=> smul_comm (_:ℂ) _ _)
-- labels any high across horizon
lemma regard (p:Label G d)(h:p∈ Grade (2*m,m))(hm:0 < m) : let w:= common S (fun x=> mantra x m) d p; stance S q d p-priceCo q (-(↑(2*m):ℤ)) (dialF w) ∈ Ash q L:= by
    intro w; change _ - priceL q _ (dialF (common S _ _ p)) ∈ _;
    rw [← (F.level d).basis.sum_repr p,map_sum,map_sum,map_sum,map_sum,← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i hi; simp_rw [map_smul,← smul_sub]; by_cases he:(F.level d).grades i=(2*m,m); swap; · rw [show (F.level d).basis.repr p i=0 from (F.level d).power_coefficient i (Ne.symm he) h];simp
    apply Submodule.smul_mem; rw [common_name]; let X:= useWord S i; have ht : X.d=2*m:= congr_arg Prod.fst he; let P:= stance S q d ((F.level d).basis i); let T:= mantra X m; let H:= priceCo (G:=G) q (-(↑(2*m):ℤ)); let A:= Grow.looking X
    change P-H (dialF T)∈_; rw [show P-H _= (P-priceCo q (-(X.d:ℤ)) A)+priceCo q (-(X.d:ℤ)) (A-dialF T) from ?_]; swap; · ext1 i; simp only [Pi.add_apply,priceCo,Pi.sub_apply,smul_sub]; rw [ht]; unfold H priceCo; abel
    refine Submodule.add_mem _ (?_) (ash_vertex X.d hq (initial_look X ht ?_).2); swap; · exact congr_arg Prod.snd ((base_grade F i).trans he)
    unfold P; rw [funext (fun k:ℕ=>stanza_name (q:=q) (k:=k) S i)]; exact ash_leaf hq X
lemma high_view (p:Label G d)(h:p∈Grade (2*m,m)) : let w:= common S (fun x=> mantra x m) d p; liftCut (m+1) (highs q χ S d p)-priceCo q (-(↑(2*m):ℤ)) (call dialF glove w) ∈ Ash q (⊤:Submodule ℝ (Fan G)):= by
    intro w; change _ - priceL q _ (call _ _ (common S _ _ p))∈_; rw [← (F.level d).basis.sum_repr p,map_sum,map_sum,map_sum,map_sum,map_sum,← Finset.sum_sub_distrib]; apply Submodule.sum_mem; intro i hi; simp_rw [map_smul,← smul_sub]; by_cases he:(F.level d).grades i=(2*m,m); swap; · rw [show (F.level d).basis.repr p i=0 from (F.level d).power_coefficient i (Ne.symm he) h];simp
    apply Submodule.smul_mem; rw [common_name,high_name]; let X:=useWord S i; have ht:X.d=2*m:= congr_arg Prod.fst he; have hx(k:ℕ): liftCut (m+1) (mature q S X χ) k=_:= stride X S χ ht
    change liftCut (m+1) _ - priceL _ _ _∈ _; change liftCut _ (mature q S X χ) - priceL q _ _∈ _; rw [funext hx,← ht,show priceCo q _ _=priceL q (-(X.d:ℤ)) (Heat.Top.cut (m+1) (bookMark X 1)) from rfl, ← map_sub]; exact ash_vertex X.d hq (sum_stone X ht).2
omit hq
lemma stiff (p:Label G d)(h:p∈ Grade (2*m,m))(i:ℕ) : duty (highs q χ S d p i) (m+1):= by
    rw [← (F.level d).basis.sum_repr p,map_sum,Finset.sum_apply]; apply duty.costs; intro j _; rw [map_smul, Pi.smul_apply]; by_cases he:(F.level d).grades j=(2*m,m); · rw [high_name]; apply duty.scalar; refine (overflow (useWord S j) S χ).more ?_; rw [use_weight,show wt F j=2*m from congr_arg Prod.fst he]; omega
    rw [show (F.level d).basis.repr p j=0 from (F.level d).power_coefficient j (Ne.symm he) h,zero_smul]; exact duty.zero
end YM.PositionX.Tot

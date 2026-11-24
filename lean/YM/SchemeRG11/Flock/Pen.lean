import YM.SchemeRG11.Flock.Slice
import YM.SchemeRG11.Plate.Total
/-! Top symbol readout. Evaluation on unscaled Taylor coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Outlook
open Function Lattice Pert Maxwell Flock Bare Tree Bark Haze Pile Atoll MvPolynomial Crest Labels
variable {G:Gauge} {n d:ℕ}
abbrev Sketch(G:Gauge)(n:ℕ):= Paper (Sky G n) ℝ
variable (n)
def vane(v:Atoll.Shaft G):Stem (Sky G n) ℝ:=∑ i:Sky G n,Finsupp.single i (cant (plum i) v)
variable {n}
def lump(x:Sky G n→ℝ):trunk G ℤ:=∑ i:Sky G n,x i • plum i
lemma vane_tr (x:Sky G n→ℝ)(s:Atoll.Shaft G): sense x (vane n s)=cant (lump x) s:=by
 rw [lump,vane,map_sum]; simp only [sense,Finsupp.linearCombination_single,cant,Finset.sum_apply,WithLp.ofLp_sum,Pi.smul_apply, PiLp.smul_apply]; exact Finset.sum_congr rfl fun _ _=>mul_comm ..
variable (n)
abbrev inlay(G:Gauge)(n:ℕ): vellum G→ₐ[ℝ] Sketch G n:=vary (vane n)
abbrev showP(G:Gauge)(n:ℕ): pLabel G→ₐ[ℝ] Sketch G n:=(inlay G n).comp (stemZero 1)
lemma rise_cast(x:Sky G n→ℝ)(q:vellum G):aeval x (inlay G n q)= aeval (cant (lump x)) q:=by rw [varyV]; simp_rw [vane_tr]
def soul(A:trunk G ℤ): Labels.Jet G:=fun m=> wideLinear G m 1 0 A
def rune(A:Labels.Jet G)(i:Key G):ℝ:= (axes G i.1).coord i.2 (A i.1)
lemma worker (i:Key G)(A:trunk G ℤ):sense (cant A) (Atoll.leafProbe 1 i)=rune (soul A) i:=by unfold rune soul; simp only [leafProbe,one_zpow,one_smul,alpha_at,secular]
lemma work (A:trunk G ℤ)(p:pLabel G): aeval (cant A) (stemZero 1 p)= aeval (rune (soul A)) p:=by rw [varyV]; simp_rw [worker]
lemma lens (x:Sky G n→ℝ)(p:pLabel G):aeval x (showP G n p)= aeval (rune (soul (lump x))) p:=by rw [showP,AlgHom.comp_apply,rise_cast, work]
lemma run_map (i:Key G)(x:Sky G n→ℝ):rune (soul (lump x)) i=∑j:Sky G n,x j *rune (soul (plum j)) i:=by unfold rune soul lump; rw [_root_.map_sum,_root_.map_sum]; simp only [_root_.map_smul,smul_eq_mul]
lemma rune_zero (j:Key G)(v:Sky G n)(h:inkAge v<generation j): rune (soul (plum v)) j=0:=by
 have he:=clouded v; unfold rune soul plum; rw [width_zero _ _ (team_height _ he),map_zero]; unfold generation at h; omega
lemma vertical (j:Key G)(v:Sky G n)(h:¬ lineP v):rune (soul (plum v)) j=0:=by obtain ⟨p,_,_,e⟩:=plunges _ h; unfold rune soul plum; rw [← e, up_zero,map_zero]
lemma advertised (i:Key G): showP G n (X i)= ∑ v:Sky G n,rune (soul (plum v)) i • X v:=by apply MvPolynomial.funext; intro x; simp_rw [← aeval_eq_eval]; rw [lens,map_sum,aeval_X,run_map]; apply Finset.sum_congr rfl; intro v _; rw [map_smul,aeval_X]; exact mul_comm ..
open scoped Classical
def liftP (i:Key G): Sketch G n:= ∑ v:Sky G n, if generation i=inkAge v then rune (soul (plum v)) i • X v else 0
lemma high_ad (i:Key G):Starts inkAge (generation i) (showP G n (X i)) (liftP n i):=by
 rw [advertised,liftP]; apply pool; intro v _
 let f : Sketch G n:= rune (soul (plum v)) i • X v
 have hx:f ∈ weightedHomogeneousSubmodule ℝ inkAge (inkAge v):= Submodule.smul_mem _ _ (isWeightedHomogeneous_X ..)
 have he:=begins (f:=f) hx
 by_cases hu:generation i=inkAge v
 · simp only [hu, if_true]; exact he
 rw [if_neg hu]; rcases lt_or_gt_of_ne hu with a|a
 · exact ⟨(MvPolynomial.mem_restrictSupport_iff ℝ).mpr (fun k hk=> le_trans a.le (ranks he.1 hk)),spike he.1 a⟩
 rw [rune_zero n i v a,zero_smul]; exact begins (isWeightedHomogeneous_zero ..) -- n variable?
lemma liftTop(p:pLabel G)(h:IsWeightedHomogeneous generation p d):Starts inkAge d (showP G n p) (aeval (liftP n) p):=cascade _ _ (fun i=>by rw [aeval_X]; exact high_ad n i) p h

def isle (x:Sky G n→ℝ)(m:ℕ):Labels.Taylor G m:=soul (lump (fun i=> if inkAge i=m+2 then x i else 0)) m
lemma lift_read(x:Sky G n→ℝ)(p:pLabel G) : aeval x (aeval (liftP n) p) = aeval (rune (isle n x)) p:=by
 have h:(aeval (R:=ℝ) x).comp (aeval (liftP n))=aeval (rune (isle n x)):=by
   ext j; rw [AlgHom.comp_apply, aeval_X, aeval_X]; unfold liftP
   rw [map_sum]
   let y (i:Sky G n) := (if inkAge i=j.1+2 then x i else 0)
   have he:=run_map n j y
   unfold rune isle
   refine Eq.trans (Finset.sum_congr rfl (fun i h=>?_)) he.symm
   unfold y generation; by_cases hu:inkAge i=j.1+2
   · rw [if_pos hu, if_pos hu.symm,map_smul,aeval_X]; exact mul_comm ..
   rw [if_neg (Ne.symm hu),map_zero,if_neg hu,zero_mul]
 exact DFunLike.congr_fun h p
lemma isle_shell (x:Sky G n→ℝ)(m:ℕ):∃ y: Maxwell.Shell G m,gaugeJet y=isle n x m:=by
 let z:=∑i:Sky G n, (if inkAge i=m+2 then x i else 0) • plume i
 have he:z∈ team G.Color (m+2):=Submodule.sum_mem _ (fun i _ => by
    by_cases e:inkAge i=m+2
    · exact Submodule.smul_mem _ _ (team_height e.le (clouded _))
    rw [if_neg e,zero_smul]; exact Submodule.zero_mem _)
 refine ⟨⟨_, conch m z he⟩,?_⟩; rw [←width z _ he]; unfold z; rw [_root_.map_sum linkup]; simp only [map_smul]; rfl

def Level (v:Sky G n) (A:Labels.Jet G):ℝ:= match v with
 | (⟨⟨0,_⟩,_⟩,_)=>0
 | (⟨⟨m+1,_⟩,Sum.inl i⟩,c)=> grove m i (A m) c
 | (⟨⟨_+1,_⟩,Sum.inr _⟩,_)=>0
end YM.SchemeRG11.Outlook

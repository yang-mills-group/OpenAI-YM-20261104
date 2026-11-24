import YM.MSbar.Alto.College
import YM.MSbar.Alto.Cotton
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
-- pre share s.Cost neighborhoods satisfy upper. p r.Wide
variable (G:Gauge)(V:Fees)(s p r:ℕ)(a:ℝ)(g:Side)
open Tuition
noncomputable def expense (r e: ℕ): ℕ:= 2*(r+3)+10*(e+2)+jewel r (e+2) (r+3) r+dyadicGrowthDegree (Whisk.ribbon 1 r) (max e 2)
noncomputable def Dean : ℕ→ℕ
| 0=>4
| i+1=> Dean i +expense (i+1) (Dean i)+1
lemma ranked : Monotone Dean:=monotone_nat_of_le_succ fun i =>by rw [Dean];omega
lemma climb(p:ℕ):p+3< Dean p :=by induction p with |zero=>change _<4;omega|succ i ih=> rw [Dean];omega
local notation "f!"=> Parma.fixP G r a V.tilt V.pre V.shape s V.axis -- check order fixP N k. adjust.
local notation "μ"=>f!/g.val
local notation "B"=> fun x=> V.lead Dean x r
local notation "K"=> Dean r
local notation "T"=> Dean (r-1)
local notation "L"=>(g.val:ℝ)
local notation "q!"=>r+1
noncomputable def shares (G:Gauge)(V:Fees)(g:Side)(r s:ℕ)(a:ℝ) := Parma.fixP G r a V.tilt V.pre V.shape s V.axis/g.val
noncomputable def topV (G:Gauge)(V:Fees)(g:Side)(r s:ℕ)(a w:ℝ):= let A:=V.lead Dean w r; fixedG G g r a V.tilt V.pre V.shape s V.axis*(w^4*A)+ w^(r+1+1)*plaqueR (r+1) r V.c4 A V.farms V.c3 V.c2+w^(r+1+1)*sherry G r (r+1) s V.c1 (a/(g.val:ℝ)) A
variable (he :0 < r)
include he
lemma spare : expense r T < Dean r:=by obtain ⟨r,rfl⟩:=Nat.exists_eq_succ_of_ne_zero he.ne'; rw [Nat.succ_sub_one,Dean]; change expense (r+1) (Dean r)< _; omega
lemma basisB : Tuition (fun x=> V.lead Dean x r) (max T 2):=unionT (front T) (scaled _ (front 2))
lemma combs : Tuition (fun x=>topV G V g r s a x) (expense r T) :=by
   let Ct(i:ℝ):=B i; let d:=max T 2; let W:= expense r T; have hh:Tuition Ct d:= basisB V r he; let D:=dyadicGrowthDegree (Whisk.ribbon 1 r) d
   unfold topV; apply same; apply same
   · apply strong (scaled _ (solder (front 4) hh)); unfold expense; omega
   · have hv₀ : Tuition (fun x=> V.farms+ totalP (r+1) r (Ct x) V.c3) d:= by apply same (act _ _); unfold totalP; simp_rw [mul_comm (Ct _)]; exact Tuition.scaled _ hh
     have he := scaled (V.c2^(r+1+1)) (river 1 d (r+1) r V.c4 _ hv₀)
     refine strong (solder (front (r+1+1)) he) ?_; unfold expense d;omega
   refine strong (solder (front (r+1+1)) (scaled _ (scaled _ hh))) ?_; unfold expense d; omega -- brace?
lemma salary_le : expense r T ≥ jewel r T (r+3) r+T:=by
    have hh:jewel r T (r+3) r ≤ jewel r (T+2) (r+3) r:=by unfold jewel;gcongr <;> omega
    unfold expense; omega
noncomputable def spat (G:Gauge)(V:Fees)(g:Side)(s r:ℕ)(a w:ℝ):= V.coin G g w s r a (purse Dean w r) (V.lead Dean w r)
lemma brush : Tendsto (fun x=> spat G V g s r a x/x^K) atTop (𝓝 (shares G V g r s a)):=by
   have h₀:= Tuition.down (combs G V s r a g he) (spare r he)
   let V':= V.c2^(r+1+1)*Parma.plaque r (r+1) V.c3 V.c4
   have hp : Tendsto (fun t:ℝ=> V'/t^2) atTop (𝓝 0):=tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
   let s':=shares G V g r s a
   have hx := ((tendsto_const_nhds (x:=s')).add h₀).add hp
   rw [add_zero,add_zero] at hx; refine hx.congr' ?_; filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
   unfold V' s' topV spat shares Fees.coin Parma.chem; dsimp only; unfold purse; field_simp; ring
lemma risePost : Tendsto (fun x=> (spat G V g s r a x+Bronze.salary r (x^T) (x^T))/x^K) atTop (𝓝 (shares G V g r s a)):=by simp_rw [add_div]; simpa only [add_zero] using (brush G V s r a g he).add (Tuition.down (salvo r T) ((salary_le r he).trans_lt (spare r he)))
lemma clears : Tendsto (fun x:ℝ=> ((spat G V g s r a x +Bronze.salary r (x^T) (x^T))/x^2+Bronze.straw (x^T) r)/x^K) atTop (𝓝 0):=by
    let f(x:ℝ):= (spat G V g s r a x+ Bronze.salary r (x^T) (x^T))/x^K; have he':Tendsto (fun x:ℝ=> f x/x^2) atTop (𝓝 0):= by have hh := ((risePost G V s r a g he).mul ((show Tendsto (fun x:ℝ=>(1:ℝ)/x^2) atTop (𝓝 0) from tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))))); rw [mul_zero] at hh; refine hh.congr' ?_; filter_upwards with x; unfold f; ring
    have hp:=spare r he; have h₀:2*T<K:=by unfold expense at hp; omega
    have hv : Tuition (fun x:ℝ=> Bronze.straw (x^T) r) (T*2):= powered (scaled (↑(r+1:ℕ)) (front T)) 2
    simp_rw [add_div]; have hc:=he'.add (Tuition.down hv (show T*2<K by omega)); rw [add_zero] at hc; refine hc.congr' ?_; filter_upwards with t; unfold f; ring
end YM.MSbar.Alto

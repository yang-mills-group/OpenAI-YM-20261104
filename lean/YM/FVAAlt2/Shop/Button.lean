import YM.FVAAlt2.Shop.Width
/-! Slot test with geometric dimension of the incoming physical A legs. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source Source.Drops
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape)
open MS MS.Koszul MS.Native MS.Landau MS.Landau.Detect MS.Plane MS.Tone MS.Theater
open Next.Foundations
open scoped Interval Topology ContDiff
variable {G:Gauge}{d k:ℕ}
local notation "Λ"=> Comparison.Stencils.Corona.act -- conflicts Shop.Λ notation ident
local notation "Θ"=> Lane4 G
local notation "P"=> hands G
local infix:70 " ⋄ "=> product ( hands G )
local notation "I"=> Complex.I
local notation "Pr"=> PertExtension.Heat.Ray.print

lemma registry(n a:ℕ)(f:ℝ→ℂ)(h:ContDiff ℝ ∞ f) : reading (a+n) (fun t:ℝ=> (t:ℂ)^a * f t)=reading n f:=by
 let g:=fun t:ℝ=>t^a • (1:ℂ)
 rw [show (fun t:ℝ=> (t:ℂ)^a * f t)=fun t=> g t*f t from funext fun t=>by simp [g,Complex.real_smul] ]; rw [read_mul (by fun_prop (disch := unfold g; fun_prop)) h]; simp_rw [g,read_pow (1:ℂ), ite_mul,one_mul,zero_mul]; simp
lemma registrSmooth(a:ℕ)(f:ℝ→ℂ)(h:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (fun t:ℝ=> (t:ℂ)^a * f t):= (Complex.ofRealCLM.contDiff.pow _).mul h
lemma pot_read(j a:ℕ)(f:ℂ) : reading j (fun t:ℝ=> (t:ℂ)^a * f) = if a=j then f else 0:=by simpa [Complex.real_smul] using read_pow (j:=j) f a
lemma read_sub {f g:ℝ→ℂ}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g)(a:ℕ): reading a (fun x=>f x-g x)=reading a f-reading a g:= by simp_rw [sub_eq_add_neg,← neg_one_mul (g _)]; rw [read_add hf (contDiff_const.mul hg), read_const, neg_one_mul]
-- degree-n jet after including common width factor and t^arity

def curlw (p:Θ)(x:Crumb G):ℂ:=Λ (Tally x.1) fun a=> onew (a,x.2) p
lemma Ωcurl (x:Crumb G): (Ψ G (Pict G (MvPolynomial.X x))).val=Koszul.mono (fun p=>curlw p x):=by
 unfold Pict; rw [MvPolynomial.aeval_X, act_simple x.1.offset x.1.plaq]; simp only [Ψ,map_sub,map_add,MvPolynomial.aeval_X,Submodule.coe_add,Submodule.coe_sub]; funext l; unfold onevar; rcases l with _|⟨l,_|_,l⟩; exact (by change (0:ℂ)+0-0-0=0; norm_num); exact (act_simple x.1.offset x.1.plaq (fun a=>onew (a,x.2) l)).symm; change (0:ℂ)+0-0-0=0; norm_num
lemma ex_leg (x:Crumb G)(p:Θ): ContDiff ℝ ∞ (fun t=>curlw (hits p t) x):= by unfold curlw; simp_rw [act_simple x.1.offset x.1.plaq]; exact (((edge_s _ _).add (edge_s _ _)).sub (edge_s _ _)).sub (edge_s _ _)
lemma lensEdge (i:Mind G Cover)(p:Θ): ContDiff ℝ ∞ (fun t=> lensw p t * onew i (hits p t)):= (lenswSmooth p).mul (edge_s i p)
lemma curl_m (x:Crumb G)(p:QP)(c:G.ColorIndex)(a:Axis)(n:ℕ): reading n (fun t=> lensw (ψ a c p) t * curlw (hits (ψ a c p) t) x) = I^n * curlLeg x n (speak n a p (cl G c)):=by
 unfold curlw; simp_rw [act_simple x.1.offset x.1.plaq, mul_sub, mul_add]; rw [read_sub (((lensEdge ..).add (lensEdge ..)).sub (lensEdge ..)) (lensEdge ..),read_sub ((lensEdge ..).add (lensEdge ..)) (lensEdge ..), read_add (lensEdge ..) (lensEdge ..)]; simp_rw [loanAll,met_proj,act_simple x.1.offset x.1.plaq]; simp [mul_add,mul_sub] -- binder change adap

lemma curl_slot (n:ℕ)(p:Θ)(x:Crumb G): reading (n+1) (fun t:ℝ=> lensw p t * curlw (hits p t) x) = Theater.RowLeg G n (offLeg x n) p:=by
 rcases p with ⟨⟨⟨_|a,b⟩,c⟩,p⟩ <;> cases b
 case some.false=>
    let v:=ψ a c p; let y:=speak (n+1) a p (cl G c)
    refine (curl_m x p c a (n+1)).trans ?_; -- explicit? defeq issue
    change I^_ * curlLeg x _ y= I^_ * curlLeg x _ ( Theater.step_in G n ( yard G n y))
    rw [ Theater.taxiY,been _ x ]
 all_goals
    unfold curlw; simp_rw [act_simple x.1.offset x.1.plaq]; simp_rw [ hits, onew,paywave, formAt ]; simp [Cylinder.way, reading, Theater.RowLeg, Theater.StarView, Theater.shutter, Theater.valueC, Landau.gauge];
lemma curl_cash (p:Θ)(x:Crumb G): reading 0 (fun t:ℝ=> lensw p t * curlw (hits p t) x)=0:=by
 rcases p with ⟨⟨⟨_|a,b⟩,c⟩,p⟩ <;> cases b
 case some.false=> refine (curl_m x p c a 0).trans ?_; rw [curlLeg_zero _,mul_zero ]
 all_goals
    unfold curlw; simp_rw [act_simple x.1.offset x.1.plaq]; simp [ hits, onew,paywave, formAt,Cylinder.way,reading,Landau.gauge]

-- label-side rescaling by its engineering markers
abbrev zΛ (t:ℝ) (x:Key G): Pol G:= (t:ℂ)^(generation x) • MvPolynomial.X x
def age (t:ℝ) : Pol G →ₐ[ℂ] Pol G:= MvPolynomial.aeval (zΛ t)
lemma ageLeg (t:ℝ)(x:Crumb G)(k:ℕ): age t (page k (offLeg x k))= (t:ℂ)^(k+2) • page k (offLeg x k):=by unfold page age LabelC; simp_rw [map_sum,map_smul,MvPolynomial.aeval_X,zΛ, generation, Finset.smul_sum]; exact sum_congr rfl fun i _=> smul_comm ..
abbrev targetK (d:ℕ)(x:Primary G)(t:ℝ): Law G:= orbit G (age t (Pr d x))
lemma onbutton (x:Crumb G)(t:ℝ): targetK d (MvPolynomial.X x) t= ∑ i∈Finset.range (d-1), (t:ℂ)^(i+2) • mono (Theater.RowLeg G i (offLeg x i)):=by unfold targetK; rw [print_vertex,map_sum,map_sum]; exact sum_congr rfl fun i _ => by rw [ageLeg,map_smul,pageX]
end YM.FVAAlt2.Shop

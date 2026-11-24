import YM.RG11Proof.Bearing.Repeat

/-!
# Mass-independent field repinning by relative degree

Leading equations in note fixed. The recursive frame and generator at each
weight are calculated simultaneously from the PRESCRIBED coupling β (order
≥2 in this version), compatible H and filtration inputs γ = b which must
obey positive powers, and engineeering grade. Content is a universal
solution, later bind to actual E. `Sealed.rule` means through precisely N, all
polynomials ordinary series. Constraints stable and uniqueness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Bearing
open YM.RG11.Jets YM.RG11.Scale PowerSeries
open scoped BigOperators Classical
variable {J:Type*}[Fintype J](w:J→ℕ)

def rephase (w:J→ℕ)(β:PowerSeries ℝ)(b N:Square J (PowerSeries ℝ)) : Square J (PowerSeries ℝ) :=
   diagonalX w*N - N*diagonalX w+ N*b + β • (flash N)

-- finite proof of compatibility & uniqueness tracks β derivative precisions.
structure Sealed (N m:Square J (PowerSeries ℝ))(β:PowerSeries ℝ)(b:Square J (PowerSeries ℝ))(k:ℕ):Prop where
    base : nearId N
    strict (i): 0 < i → i≤k → Slopes w (piece i N)
    labelled(i): i≤k → graded w (piece i m)
    empty : piece 0 m=0
    rule : MatThrough k (m*N) (rephase w β b N)

section
variable (β:PowerSeries ℝ)(b:Square J (PowerSeries ℝ))

-- implementation without supplying field/legal/scope yet.
-- recursive entries with placeholder 1 at i≥n in X base when n=0.
def novae (i:ℕ):Square J ℝ × Square J ℝ:=
   if i=0 then (1,0)
   else let p:=fun j=>if _:j < i then novae j else ((0:Square J ℝ),0)
        let u:= known β b (alien p) (takeMap p i) i
        (spot w u (fun a=> -1/a),isolate w u)
termination_by i

def north : Square J (PowerSeries ℝ):=alien (novae w β b)
def polar : Square J (PowerSeries ℝ):=tailMap (novae w β b)

def vintage(n:ℕ):Square J ℝ:=
   let p:=fun j=>if j < n then novae w β b j else ((0:Square J ℝ),0)
   known β b (alien p) (takeMap p n) n
@[simp] theorem lift_zero:novae w β b 0=(1,0):=by rw [novae]; simp
 theorem new_years (n:ℕ)(hn:0<n):novae w β b n=(spot w (vintage w β b n) (fun a=> -1/a),isolate w (vintage w β b n)):=by
   rw [novae,if_neg hn.ne']
   simp only [vintage, dite_eq_ite]
@[simp] theorem north0:nearId (north w β b):=by unfold nearId north alien; simp
@[simp] theorem polar0:piece 0 (polar w β b)=0:=by unfold polar tailMap; simp

 theorem romance (hβ:∀i≤1,coeff i β=0)(hb:piece 0 b=0)(u:J){I:Type*}{H:I→Square J ℝ}(h:∀ i,graded w (H i))(he:vertical (L:=Constraints.position u w H) b):
    let L:=Constraints.position u w H
    L.Lawful (north w β b) ∧ vertical (L:=L) (polar w β b) ∧ ∀ k, Sealed w (north w β b) (polar w β b) β b k:=by
   let N:=north w β b; let Q:=polar w β b
   let s:=novae w β b
   let L:=Constraints.position u w H
   have hp(i): piece i N=(s i).1 ∧ piece i Q=(s i).2:=⟨piece_unpack ..,piece_unpack ..⟩
   have hi(i:ℕ):
      (0 < i → Slopes w (piece i N) ∧ piece i N ∈ L.vary) ∧ (graded w (piece i Q) ∧ piece i Q ∈ L.vary) ∧ piece i (Q*N)=piece i (rephase w β b N):=by
      induction i using Nat.strong_induction_on with
      | h i ih=>
        by_cases hh:i=0
        · subst i; simp only [not_lt_zero,IsEmpty.forall_iff, true_and, N,Q,polar0]
          refine ⟨⟨graded.zero,L.vary.zero_mem⟩,?_⟩
          ext l j
          have hu:constantCoeff (R:=ℝ) β=0:= (coeff_zero_eq_constantCoeff_apply β).symm.trans (hβ 0 (by decide))
          have HN(a j):constantCoeff (N a j)=(1:Square J ℝ) a j:=(coeff_zero_eq_constantCoeff_apply _).symm.trans (congrArg (fun (z:Square J ℝ)=>z a j) (north0 w β b))
          have HQ(a j):constantCoeff (Q a j)=0:= (coeff_zero_eq_constantCoeff_apply _).symm.trans (congrArg (fun (z:Square J ℝ)=>z a j) (polar0 w β b))
          have hB(a j):constantCoeff (b a j)=0:= (coeff_zero_eq_constantCoeff_apply _).symm.trans (congrArg (fun (z:Square J ℝ)=>z a j) hb)
          simp only [piece_apply, rephase, coeff_zero_eq_constantCoeff_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,map_sum,map_sub,map_add,map_mul,hu,zero_mul]
          change ∑ x,constantCoeff (Q l x)*constantCoeff (N x j)=_
          change (∑ x,constantCoeff (Q l x)*constantCoeff (N x j)) = ((∑ x,constantCoeff (diagonalX w l x) * constantCoeff (N x j)) - (∑ x, constantCoeff (N l x)*constantCoeff (diagonalX w x j)) + (∑ x,constantCoeff (N l x)*constantCoeff (b x j))) + _
          simp_rw [HQ,HN,hB,zero_mul,mul_zero,Finset.sum_const_zero,add_zero]
          let hh:Square J ℝ:=(diagonalX w).map constantCoeff
          change _ = (hh* (1:Square J ℝ)) l j - ((1:Square J ℝ)*hh) l j; rw [one_mul,mul_one,sub_self]
        have ht:0 < i:=by omega
        let a:=vintage w β b i
        have hf: piece i N=spot w a (fun t=> -1/t) ∧ piece i Q=isolate w a:=by
           rw [(hp i).1,(hp i).2]; unfold s; rw [new_years _ _ _ i ht]
           exact ⟨rfl,rfl⟩
        let p:=fun j=>if j < i then s j else ((0:Square J ℝ),0)
        have H(j)(hj:j < i):piece j N=(p j).1 ∧ piece j Q=(p j).2:=by unfold p; rw [if_pos hj]; exact hp j
        have hknown:known β b N Q i=a-piece i Q:=fresh hβ hb (north0 w β b) (polar0 w β b) ht p H
        have hv: L.Lawful (alien p):={
            baseline:= (show piece 0 (alien p) = _ by simp [alien,p,ht,s])
            positive:=(fun {m} k=> by
              unfold alien; rw [piece_unpack]; by_cases hv:m < i
              · rw [←(H _ hv).1]; exact ((ih _ hv).1 k).2
              simp [p,if_neg hv]) }
        have hv': vertical (L:=L) (takeMap p i):=by
            intro k; unfold takeMap; rw [piece_unpack]; split <;> rename_i hn
            · rw [←(H _ hn).2]; exact (ih _ hn).2.1.2
            exact L.vary.zero_mem
        have hy:a∈L.vary:= ((vertical.add (vertical.left he hv) (vertical.waive β (vertical.flash hv))).sub (vertical.right hv' hv)) i
        rw [hf.1,hf.2]; refine ⟨fun _=> ⟨on_rail w hy _ (by simp),spot_across w u h hy _⟩,⟨graded.isIsolated _, (Permits.position h u).split hy⟩,?_⟩
        have hh : spot w (piece i N) id +known β b N Q i=0:=by rw [hknown,hf.1,hf.2,← add_sub_assoc,disperses,sub_self]
        rw [←sep, show diagonalX w*N-N*diagonalX w+(N*b+β • flash N-Q*N)= rephase w β b N - Q*N from by unfold rephase; abel] at hh
        have hy : piece i (rephase w β b N)-piece i (Q*N)=0:=by rw [← hh]; ext l t; simp
        exact (sub_eq_zero.mp hy).symm
   exact ⟨⟨north0 w β b,fun hk=> ((hi _).1 hk).2⟩, fun j=>(hi j).2.1.2, fun j=>⟨north0 w β b,fun i hn _=>((hi i).1 hn).1,fun i _=>(hi i).2.1.1,polar0 w β b, MatThrough.of_piece (fun i _=>(hi i).2.2)⟩⟩
end
end YM.RG11.Bearing

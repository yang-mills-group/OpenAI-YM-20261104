import YM.FormalBulk08.Cork.Weights

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Cork
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries
open Lotus Shore Mesa Gorge City
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {A σ : ℝ}

def ka (R:Row (TypeFace 2) (TypeFace 2)) := composeRows (composeRows (transRows (cobound 1)) R) (cobound 1)

def plen (a b:Axis)(h:a≠b): TypeFace 2:= ⟨{a,b},by simp [h]⟩
lemma left_peg (a b:Axis)(h:a≠b)(u: TypeFace 2): left ℝ 1 b u (coord a)= if u=plen a b h then parity u.val b ℝ else 0:= by
   unfold left; rw [Matrix.of_apply]; by_cases hp:u=plen a b h
   · subst u; have hh : ({a,b}:Finset Axis).erase b={a}:= by ext k;simp;grind
     simp [plen,remove,coord,hh,Ne.symm h]
   rw [if_neg hp]; split_ifs with he hu
   · have hh : u.val.erase b = {a}:=congr_arg Subtype.val hu
     exact False.elim (hp (Subtype.ext (by change _=({a,b}:Finset Axis); rw [←Finset.insert_erase he,hh];ext;simp [or_comm])))
   all_goals rfl
lemma twice_peg (a b:Axis)(h:a≠b): ∑ u: TypeFace 2,left ℝ 1 b u (coord a)*left ℝ 1 b u (coord a)=1:= by
   simp_rw [left_peg a b h]; rw [Finset.sum_eq_single (plen a b h)];swap;· intro u _ hu;rw [if_neg hu,mul_zero]
   swap;· simp
   rw [if_pos rfl, Exterior.parity,←mul_pow];simp

lemma raw_value {R: Row (TypeFace 2) (TypeFace 2)} (H:R.strip σ A)(hp:0<σ)(h:R.read 0=1)(a b:Axis)(ha:a≠b): scales (ka R (coord a) (coord a)) (ch b * ch b)= -2:= by
   have hX (p q:Axis): fshade (frow (ch b*ch b) p) q= if p=b ∧ q=b then (fun _=> -2) else (0:Cover→ℝ):= by
       by_cases he:p=b <;> by_cases hq:q=b <;> ext <;> simp [he,hq,Ne.symm,fshade,frow,ch]; ring
   rw [ka,cash_crest H ((Pad.ch b).mul (Pad.ch b)) hp]
   have hz (i j: TypeFace 2) (k l : Axis): scales (R i j) (fshade (frow (ch b*ch b) k) l)= if k=b ∧ l=b ∧ i=j then -2 else 0 := by
      have he:= congr_fun (congr_fun h i) j; simp only [Row.read,Matrix.of_apply,Laurent.read, mode_constant,one_smul,←Complex.ofReal_tsum,Matrix.one_apply] at he
      rw [scales,hX]; by_cases h':k=b ∧ l=b
      · rw [if_pos h']; split_ifs with H; rw [tsum_mul_right]; have hh : ∑' u,R i j u=(1:ℝ):= by rw [if_pos H.2.2] at he; exact_mod_cast he
        rw [hh,one_mul]
        case neg=>
         rw [tsum_mul_right]; have HH : i≠j := fun e=>H ⟨h'.1,h'.2,e⟩; rw [if_neg HH] at he; have hh : ∑' u,R i j u=(0:ℝ):=by exact_mod_cast he
         rw [hh,zero_mul]
      rw [if_neg h',if_neg (fun hh=>h' ⟨hh.1,hh.2.1⟩)];simp
   simp_rw [hz];
   have ht i k u : ∑ x:Axis,left ℝ 1 x u (coord a)* (if k=b ∧ x=b ∧ u=i then -2 else 0)= if k=b ∧ u=i then left ℝ 1 b u (coord a)*(-2) else 0 := by by_cases hh:k=b <;> by_cases he:u=i <;> simp [hh,he,mul_ite]
   simp_rw [ht]
   let L x:= left ℝ 1 b x (coord a)
   have hu i k : ∑ x: TypeFace 2, (if k=b ∧ x=i then L x * (-2) else 0)= if k=b then L i *(-2) else 0 := by by_cases h:k=b <;> simp [h]
   unfold L at hu; simp_rw [hu,mul_ite,mul_zero]; simp only [Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte];simp_rw [←mul_assoc];rw [←Finset.sum_mul,twice_peg a b ha,one_mul]

lemma sand_pair {U:Type*} (T: Tile U 2) (a b) : sand T ![a,b]= (1/2:ℝ)*(T ![a,b]+T ![b,a]):= by
   let t:=Equiv.swap (0: Fin 2) 1
   have he:(1:Equiv.Perm (Fin 2))≠t:=fun e=> by have hh:=DFunLike.congr_fun e 0;exact absurd hh (by decide)
   have h:(Finset.univ : Finset (Equiv.Perm (Fin 2)))={1,t} := Eq.symm (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [he,Fintype.card_perm,Nat.factorial_succ]));
   rw [sand,h, Finset.sum_pair he,show ![a,b] ∘ (↑t)=![b,a] by ext1 i;fin_cases i <;> rfl]; simp only [Equiv.Perm.coe_one, Function.comp_id,Fintype.card_perm,Fintype.card_fin,Nat.factorial_succ]; norm_num;ring
-- reader coefficient needed EXACT
lemma hem_pair (R:Row (TypeFace 2) (TypeFace 2)) (a:Axis)(i:hue G)(v) :
   hem (setkin G R) a a i i v=(-1/4:ℝ)*(ka R (coord a) (coord a) (-v)+ka R (coord a) (coord a) v):= by
   rw [hem,setkin, sand_pair]; simp [lands,inkling,Flat.shadedRows,ka,halve,couple]; ring

def value (i : hue G)(T : Slopes G):= mir T (1:Axis) 1 i i 0 0
lemma weighed {R: Row (TypeFace 2) (TypeFace 2)} (H:R.strip σ A)(hp:0<σ)(h:R.read 0=1)(i:hue G): value i (setkin G R)=1 := by
   let a:= (1:Axis); let b:= (0:Axis); have hb:a≠b:=by decide
   let K:= ka R (coord a) (coord a); let f:=ch b*ch b
   have he: (∑' v,K v*f v)=-2:= raw_value H hp h a b hb
   obtain ⟨E,hE,H'⟩:= Next.Free.delta_budget 1 σ
   have hx:Summable (fun v=>K v*f v):= pay_pivot _ _ ((strip_compose hp.le (strip_compose hp.le (strip_trans H') H) H') (coord a) (coord a)) ((Pad.ch b).mul (Pad.ch b)) hp
   have h1 := (Equiv.neg Cover).summable_iff|>.mpr hx
   have ht v : f (-v)=f v:=by simp [ch,f]
   change (∑' v, hem _ a a i i v * f v)=1; simp_rw [hem_pair,mul_assoc,add_mul, tsum_mul_left];change (-1/4:ℝ)*(∑' v:Cover,(K (-v)*f v+K v*f v))=_
   rw [Summable.tsum_add _ hx, he]; swap;· simpa only [Function.comp_def,Equiv.neg_apply, ht] using h1
   rw [← Equiv.tsum_eq (Equiv.neg Cover)]; simp only [Equiv.neg_apply,neg_neg,ht,he];norm_num
lemma pink_weigh {j : ℕ} (k : ℝ)(hk:0<k)(hj:4≤j)(v:Next.Free.Train j)(i:hue G) : value i (setkin G (Next.Free.pink k v))=1:= by
   obtain ⟨σ,C,hs,hC,H,-⟩:=Flat.colors G k hk hj; refine weighed (H v).1 hs ?_ i
   exact ((Next.Free.heart_true k hk hj v).1.echo 0 (by simpa only [mon_zero] using Next.Free.mon_mem 1 (0:Site 1))).trans (Next.Free.pulse_zero ..)
end YM.FormalBulk08.Cork

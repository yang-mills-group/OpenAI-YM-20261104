import YM.WilsonBridge.Hats
import YM.WilsonBridge.Hessian

/-!
# Full periodic position chart, letters and bare kinetic data

This is precisely the ambient alphabet of YM.MS.Fleet.PhysicalSum. Don't make an
acyclicity assertion here (harmonics!). Fourier conventions for Landau block proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Full
open MS MS.Book MS.Swirl MS.Koszul MS.Cylinder MS.City MS.Latch MS.Fleet MS.Landau
open MS.Book.Program Book.Convolve MS.Plane Cylinder.Lab Tone Mesh MS.Native MS.Tone Lattice MS.Orbit MS.Orbit.Cog
open Function Finset FiniteDFT MS.Bare Tone.Frame
open scoped BigOperators Matrix
variable {V K A : Type}[DecidableEq V][DecidableEq K][DecidableEq A][Fintype V][Fintype K][Fintype A]
variable {G:Gauge}{n:Side}
local notation "T" H => Mode H (Site n)
variable (G n)
abbrev Glu := Mind G (Site n)
abbrev Ghost := Native.Eyes G (Site n)
abbrev Index := FixedMode G n -- momentum or whole chart, outside Cog
local notation "P" => field (Landau.parity (A:=Axis) (C:=Conn G)) (P:=Site n)
local notation "W" => docket n ( Native.Wilsonian.W G )
abbrev StampA := Axis ×Conn G
abbrev StampC := Conn G
local notation "J" => Glu G n
local notation "C" => Ghost G n
local notation "I" => Index G n
-- `T` using atom entirely. photo
private abbrev B (G:Gauge)(n:Side):= Native.Paper G (Site n)
local notation "β" => B G n
local notation "γ" => panel G (Site n)
def pictureA : J ≃ T (StampA G) where
    toFun i:= ((i.1.2,i.2),i.1.1)
    invFun j:= ((j.2,j.1.1),j.1.2)
    left_inv _:=rfl
    right_inv _:=rfl
def pictureC : C ≃ T (StampC G):= Equiv.prodComm ..
-- tags and super alphabet equivalence. yIndex looks like position full not mode
variable {G n}
def a (x:Glu G n): I := (β).plain ((γ).AId x)
def c (x:Ghost G n): I := (β).plain ((γ).KId x)
def k (x:Glu G n): I := (β).dual ((γ).AId x)
def b (x:Ghost G n): I := (β).dual ((γ).KId x)
lemma select_a {x:J} : Native.direction (Full.a x)=priv x:= Native.dirA x
lemma select_c {x:C} : Native.direction (Full.c x)=0:= rfl
lemma select_k {x:J} : Native.direction (Full.k x)=0:= rfl
lemma select_b {x:C} : Native.direction (Full.b x)=0:= rfl
abbrev iA (v:Bool) : StampA G ↪ BH G := ⟨signA v ∘ Sum.inl,(signA_rec v).comp Sum.inl_injective ⟩
abbrev iC (v:Bool): StampC G ↪ BH G := ⟨signA v ∘ Sum.inr,(signA_rec v).comp Sum.inr_injective ⟩
lemma c_inj : Injective (Full.c (G:=G) (n:=n)):= by rintro ⟨x,y⟩ ⟨hx,hy⟩ h; refine Prod.ext (congr_arg Prod.snd h) (congr_arg (fun x:I=> x.1.2) h)
-- use performance tomar. Defines actual sum convention, use with bigOperator proofs
variable (G n)
def alphabet : Based.Letters J C ≃ I where
    toFun := Sum.elim (Sum.elim a c) (Sum.elim k b)
    invFun x:= match x with
       | (((some i,v),t),y)=> if v then .inr (.inl ((y,i),t)) else .inl (.inl ((y,i),t))
       | (((none,v),t),y)=> if v then .inr (.inr (y,t)) else .inl (.inr (y,t))
    left_inv := by rintro ((i|i)|(i|i))<;>rfl
    right_inv := by rintro ⟨⟨⟨_|i,_|_⟩,t⟩,y⟩<;> rfl
variable {G n}
lemma charges (x): P (alphabet G n x)=Based.parity J C x:= by rcases x with (i|i)|(i|i)<;> rfl
lemma whole {R:Type}[AddCommMonoid R](U:I→R):∑ i,U i=((∑ i,U (a i))+(∑ i,U (c i)))+((∑ i,U (k i))+(∑ i,U (b i))):= by rw [← Equiv.sum_comp (alphabet G n) U]; exact (Fintype.sum_sum_type _)|>.trans (congr_arg₂ HAdd.hAdd (Fintype.sum_sum_type _) (Fintype.sum_sum_type _)) -- notation

local notation "Z" => Chart.drive n
local notation "γΦ"=> Focus.launch ( Native.glow G (Site n) ) (colorTerm G (Site n)) ( Chart.loco ( Chart.drive n ))
variable (G n)
def H : Matrix J J ℂ:= fun i j=> -(W) [a i,a j]
def X : Matrix J C ℂ:= fun i j=> (W) [k i,c j]
abbrev ChillF (t:Bool): Matrix I I ℂ:= Matrix.of (Chill (Near.Master G n t))
abbrev GU := F (BH G) n
def HalfF (t:Bool): Grain I := cov_push ( Near.Master G n t ) (GU G n)
def ChillP (t:Bool): Matrix I I ℂ:= Matrix.of (Chill (HalfF G n t))
variable {G n}
lemma voltF (t:Bool) : ChillP G n t= GU G n * ChillF G n t * GU G n:= by
    let K:= Near.Master G n t; let U:= GU G n
    have he : ChillP G n t=(2:ℂ) • (U.transpose * Matrix.of K * U):=rfl
    rw [he,← Matrix.smul_mul, ← Matrix.mul_smul, show U.transpose=U from F_sym (BH G) n]; rfl
-- actual channels of W before resolution.
lemma H_flip : (H G n).transpose=H G n:= by
   ext i j:1; have he: MS.Koszul.Symm P W:= by change MS.Koszul.Symm P (sumHome (shown n ( Native.Wilsonian.W G ))).val; rw [total_uses]; exact (Tune.sum _ (fun i _=> Tune.move (fun (z:Site n)=> i+z) (Tune.move (wrap n) (sym_all _ _ _)))).symm
   change - W [a j,a i] = - W [a i,a j]; exact congr_arg Neg.neg ((show W [a j,a i]=(1:ℂ)*W [a i,a j] from he [] (a j) (a i) []).trans (one_mul _))
-- Hessian entry W_a from action. antifield terms vanish
lemma H_entry (i j:J) : H G n i j= - ( Native.reads ( Chart.rent (G:=G) ( Chart.drive n ) ) ) [a i,a j] := by
   unfold H; rw [ Native.Wilsonian.witnessD n, Focus.Sourced,Pi.add_apply, Bonded.hung,Finset.sum_apply, Finset.sum_eq_zero ,add_zero ]; · rfl
   intro x _; let R:= Native.Paper G (Site n); let f := atLetter (R.dual x) (R:=ℂ); have he(i:J): D (Full.a i) f=0:= unheard _ (R.diff ((γ).AId i) x); rw [Pi.smul_apply]; change R.fee (R:=ℂ) x • product P f (γΦ x) [Full.a i,Full.a j]= _; rw [D_eval (Full.a i) (product P f _ ), D_product, he i,map_zero,LinearMap.zero_apply,zero_add]; change R.fee (R:=ℂ) x • product P (sign P false f) _ [a j] =_; rw [sign_id, Based.Position.product_one]; change R.fee (R:=ℂ) x • (D (Full.a j) f [] * _ + 0 * _)=_; rw [he j]; simp -- verify
lemma ghost_X (i:J)(j:C): X G n i j= projector i ( Chart.loco ( Chart.drive n ) j 0 ):= by
   unfold X; rw [ Native.Wilsonian.witnessD ]; change  D (Full.k i) (Focus.Sourced (Chart.rent Z) (colorTerm G (Site n)) (Chart.loco Z) (Native.glow G (Site n))) [Full.c j]=_
   have hv: D (Full.k i) (Focus.Sourced (Chart.rent Z) (colorTerm G (Site n)) (Chart.loco Z) (Native.glow G (Site n)))=γΦ ((γ).AId i):= by
      have ht : Bonded.Lifted (Native.Paper G (Site n)) γΦ:= Focus.lifting _ _ _ ((Chart.vibes Z).smooth)
      unfold Focus.Sourced; rw [ map_add,Cylinder.Taylor.ink_off (Native.glow G (Site n)).e0 (i:=Full.k i) rfl,show Full.k i=(Native.Paper G (Site n)).dual ((γ).AId i) from rfl, ht.acted,zero_add,show (Native.Paper G (Site n)).fee (R:=ℂ) ((γ).AId i)=1 from rfl,one_smul]
   rw [hv,Focus.launch_stone, Focus.stone,Finset.sum_apply,Finset.sum_eq_single_of_mem j (mem_univ j)]; swap; · intro i hi h; rw [Based.Position.product_one]; change atLetter (Full.c i) [Full.c j]*_+0*_= _; rw [notNamed _ (fun hh=>h (c_inj hh.symm)),zero_mul,zero_mul,add_zero]
   rw [Based.Position.product_one]; change atLetter (Full.c j) [Full.c j] * (projector i _:ℂ) + 0 * _ = _; rw [speaks,one_mul,zero_mul,add_zero]
-- super blocks extraction
abbrev at2 {V:Type} (X:Raw V ℂ) : Matrix V V ℂ:= fun i j=> X [i,j]
omit [DecidableEq V] [DecidableEq K] [Fintype K] in
lemma pull_two (X:Raw V ℂ) (U:Matrix K V ℂ): at2 (pull U X)=U * at2 X * U.transpose := by
    ext i j:1; change pull _ X [i,j]=_
    have he : ∀ u:K, ∀ H:Raw V ℂ, pull U H [u]=∑ x:V,U u x * H [x] := fun u H=> by rw [D_eval u (pull U H),pull_drop]; simp [ Finset.sum_apply ]
    rw [ D_eval i (pull U _),pull_drop ]; simp_rw [ Finset.sum_apply,Pi.smul_apply,he, Matrix.mul_apply,smul_eq_mul,Finset.mul_sum, Finset.sum_mul ]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> by simp [at2,mul_comm,mul_left_comm]
lemma origH : pull (GU G n) W= Bulk G n ( sleeve lace (Tone.run (Native.Wilsonian.W G))):= through_sum _
lemma restH : Near.flatH G n = pull (GU G n) (mask 2 W):= by
   change Bulk G n ( sleeve lace (Tone.run (Native.Wilsonian.core G 0)))=_; rw [ ← through_sum, Native.Wilsonian.at_rest ]; congr 1; exact Book.enterShim (b:=true) n _ -- implicit?
lemma up_kinetic : at2 ( Near.flatH G n )=GU G n * at2 W * GU G n := by rw [restH,pull_two, F_sym (BH G) n ]; congr 2
-- Fourier of any two slots. color handling in reindex hat proof later.
abbrev mid (f:V→K) {n:Side}: Mode V (Site n)→ Mode K (Site n):= fun i=> (f i.1,i.2)
lemma picture (e:V↪ A)(d:K↪ A)(M:Matrix (T A) (T A) ℂ): ( F A n*M*F A n ).submatrix (mid e) (mid d) = F V n * M.submatrix (mid e) (mid d) * F K n:= by
    have he (e:V↪ A)(k:T V)(U: (T A)→ℂ): ∑ i:T V, F V n k i * U (mid e i)= ∑ i:T A, F A n (mid e k) i * U i := by simp [F,mid,Fintype.sum_prod_type,ite_mul]
    have hd (e:K↪ A)(k:T K)(U: (T A)→ℂ): ∑ i:T K, F K n i k * U (mid e i)= ∑ i:T A, F A n i (mid e k) * U i:= by simp [F,mid,Fintype.sum_prod_type,ite_mul]
    ext i j:1
    simp_rw [ Matrix.submatrix_apply, Matrix.mul_apply ]; -- factor inner
    simp_rw [ mul_comm _ ( F A n _ (mid d j)), mul_comm _ ( F K n _ j ) ]; rw [ ← hd d j (fun x=>(∑ k:T A, F A n (mid e i) k * M k x)) ]; refine Finset.sum_congr rfl (fun x _=>?_); rw [ show ∑ x_1:T V, F V n i x_1 * M.submatrix (mid e) (mid d) x_1 x= ∑ x_1:T A, F A n (mid e i) x_1 * M x_1 (mid d x) from he e i (fun u=> M u (mid d x)) ]
end YM.WilsonBridge.Full

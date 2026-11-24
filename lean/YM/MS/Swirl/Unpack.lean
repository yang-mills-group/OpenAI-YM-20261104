import YM.MS.Swirl.TickH
import YM.MS.Fleet.Envelope
/-!
# Domain of end Wick map. Packed, but use Φa on bulk & S with det projected weights
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom
open scoped Topology ContDiff Interval
variable {A I W:Type}{G:Gauge}{i:I}{L:I→Side}{A':Faces I} {φ:Team}{n:ℕ}{N:Side} {Q:ℕ→ I→Law G} {V: Actor G} [LinearOrder W] {b:Bool}{η:I→ℝ}
-- stripped team
abbrev Stripped (t:Team):Team:= fun i=> ⟨0,0,(t i).coupling⟩
lemma bareShift (t:Team): shift (Stripped t)=shift t:=rfl
lemma numb (t:Team)(x:ℝ)(a:Atom Axis): adap (Stripped t) a x=1:= by
   have he : affirmative 0 x = 1:= by ext k; simp [affirmative,PowerSeries.coeff_one]
   have hm : opposite 0 x=1:= by rw [ ← pairs (0) x,he,one_mul]; -- wrong orientation simplifies both 1's
   rcases a with ⟨_|i,_|_⟩ <;> first| exact he| exact hm
lemma TrainL (k:ℕ)(F:Dot G Cover)(x:ℝ)(t:Team): train (Y ( Stripped t ) x) k F= if k=0 then F else 0:= by
    have he : Y ( Stripped t ) x= fun _:LightMode G Cover=>(1:Cn):= funext fun i=> numb t x i.1.1
    apply Subtype.ext; funext l; rw [he, train_v,offer ]; have hv (l:List (LightMode G Cover)): (l.map (fun _=>(1:Cn))).prod=1:= by induction l with| nil=>rfl| cons a l ih=>simp
    rw [hv,PowerSeries.coeff_one]; split <;> simp -- inspect
lemma strip_wobble (t:Team)(x:ℝ): wobble G (Stripped t) x=substitute (P:=Dot G Cover) (shift t x):= by
   apply LinearMap.ext; intro F; funext n; unfold wobble; rw [LinearMap.comp_apply,bareShift]; change car ( Y ( Stripped t ) x ) _ _ = _; rw [ rolls ]; simp_rw [ TrainL ]; rw [ Finset.sum_eq_single_of_mem (0,n) (by simp), if_pos rfl ]; intro j hj hh; obtain he:=Finset.mem_antidiagonal.mp hj; exact if_neg (fun h=> hh (Prod.ext h (by dsimp; omega))) -- signature master
lemma gapTeam (t:Team)(x:ℝ): car (Y ( Stripped t ) x)= LinearMap.id ( M:=T ( Dot G Cover )):= by
   apply LinearMap.ext; intro F; funext i; rw [rolls]; simp_rw [TrainL]; rw [ Finset.sum_eq_single_of_mem (0,i) (by simp),if_pos rfl ]; rfl; intro j hj hh; obtain he:=Finset.mem_antidiagonal.mp hj; exact if_neg (fun h=>hh (Prod.ext h (by dsimp; omega)))
lemma sWob (t:Team)(x:ℝ)(v:T (Dot G Cover)): wobble G t x v=car ( Y t x ) (wobble G ( Stripped t ) x v):= by rw [ strip_wobble ]; rfl
-- teams.Projected bulk root
abbrev SendB (G:Gauge)(N:Side)(b:Bool): Linear ( Dot G Cover ) ( BL ( FixedMode G N ) ):= pay b • (( Bulk G N ) ∘ₗ ( sleeve lace ) ∘ₗ Tone.run)
def NRG (t:Team)(x:ℝ)(N:Side)(G:Gauge)(b:Bool): SpecB ( FixedMode G N ):= fun k=> if k=0 then 0 else SendB G N b ( style G t x k )
lemma τ_nil (t:Team)(x:ℝ)(N:Side)(G:Gauge): NRG t x N G b 0=0:=if_pos rfl
abbrev κP (G:Gauge)(N:Side)(b:Bool):= ReadP (iota G N) b
lemma Orders (t:Team)(x:ℝ)(N:Side)(G:Gauge)(b:Bool): NRG t x N G b= pointL ℕ ( SendB G N b ) ( style G t x ) - useN.refineV ( pay b • flatH G N ):= by
    funext k; unfold NRG; split_ifs with he; · rw [he,Pi.sub_apply,lone_use]; change 0=SendB G N b _ - _; unfold style; rw [whoZero, show SendB G N b (core G 0)= pay b • flatH G N from rfl,sub_self ]
    rw [ Pi.sub_apply, Puff.SplitP.refineV,if_neg (show k≠ useN.origin from he),sub_zero ]; rfl
lemma absoluteX (t:Team)(η:I→ℝ)(b:Bool)(i:I): let d:=dimT L i; B_init G L b (TokenB G t η) i=κP G d b (NRG t (η i) d G b):= by
    funext k; by_cases hp:k=0
    · rw [ hp ]; change Scan b L i (TokenB G t η 0 i)= readerV ( iota G (dimT L i) ) b ( NRG t (η i) _ G b 0 ); rw [ TokenB, if_pos rfl, map_zero, τ_nil, map_zero ]
    unfold B_init; rw [TokenB,if_neg hp ]; change _=readerV ( iota G (dimT L i) ) b (NRG _ _ _ G b k); rw [ NRG,if_neg hp ]; rfl
lemma runner (t:Team)(x:ℝ)(F:Dot G Cover)(k:ℕ): run ( train (Y t x) k F)= merit (fieldV t x ∘ Prod.fst) k ( run F ):= ( pennantC ( PowerSeries.coeff k ) F (Y t x) _ Tone.paywave (fun i j h=> (congr_arg ( fieldV t x ) ( Tone.in_light i j h )).symm) ).symm
lemma stake (t:Team)(x:ℝ)(l:Legs (FixedMode G N)): List.map (fieldV t x∘Prod.fst) (Orbit.stage l)= l.map ( inUse t x ):=by simp [Orbit.stage,List.map_map] -- simp unfold
lemma sendL (t:Team)(x:ℝ)(F:Dot G Cover)(k:ℕ)(N:Side)(b:Bool): SendB G N b ( train (Y t x) k F )= merit ( inUse t x ) k ( SendB G N b F ):= by
    funext l; unfold SendB; rw [ offer ]; simp_rw [ LinearMap.smul_apply,LinearMap.comp_apply, Pi.smul_apply,smul_eq_mul, bulkZ, Orbit.point,sleeve_here,runner, offer, stake ]; split_ifs <;> ring
local notation "ΤΩ"=> taxi (inUse φ (η i) ( n:=dimT L i ) ( G:=G ))
lemma compass (t:Team)(x:ℝ)(F:T (Dot G Cover))(N:Side)(b:Bool): pointL ℕ ( SendB G N b ) (car (Y t x) F)= taxi ( inUse t x ) ( pointL ℕ ( SendB G N b ) F ):= by funext k; change SendB G N b _ = _; rw [rolls, map_sum ]; exact Finset.sum_congr rfl fun _ _=> sendL ..
lemma βalign (F:Team)(x:ℝ)(N:Side)(G:Gauge)(b:Bool): NRG F x N G b=shiftH ( inUse F x ) ( pay b • flatH G N ) + taxi (inUse F x) ( NRG (Stripped F) x N G b ):= by
    rw [Orders,Orders]; unfold style; rw [sWob ( t:=F ),compass]; unfold shiftH; rw [map_sub]; abel
-- fee.S.sym Bulk
local notation "πA"=> σbranch ( G:=G ) ( n:=N )
variable {d:ℤ}{F: Dot G Cover}
lemma be_sym (h: Symm DotFlip F.val): Symm πA ( Bulk G N ( sleeve lace ( run F ) ) ):= by
   intro l i j r; rw [bulkZ,bulkZ,show net (l++j::i::r)= net (l++i::j::r) from (?_)]; swap; · simp only [net_append,net_cons]; abel
   rw [ Orbit.point, Orbit.point, sleeve_here,sleeve_here ]; unfold Orbit.stage; simp only [ hook,List.map_append,List.map_cons,List.prod_append,List.prod_cons ]; rw [ ( show Symm DotFlip ( run F ) from tied.sym F h ) _ ( addr i ) ( addr j ), mul_left_comm ( lace ( addr i ) ) ]; split_ifs; · ring_nf
   rw [mul_zero]
lemma memBill (h:Tuned F 0)(hf: Limit F.val (n:ℤ)): SendB G N b F∈ FeeP πA:= ⟨ ( be_sym h.symm ).smul _, minH (Limit.smul ( pay b ) ((gl_Bulk G N).lap _ n ( sail_ℓ ( oneRank hf ))))⟩
lemma μτrank : Book.rank 2 (pay b • flatH G N):= by
    intro l hl; change pay b • flatH G N l= _; unfold flatH; rw [bulkZ]; split; rw [ Orbit.point,sleeve_here,core_rank _,mul_zero,mul_zero,smul_zero ]; -- mod_int ℤ
                                                                                                                              rw [mod_int] at *; simp [Orbit.stage, hl]
    rw [smul_zero]
lemma sendEven (h:Tuned F 0): Pure πA false ( SendB G N b F ):= ( pureB ( tied.pure F ( h.parity ghostParity ) ) ).smul _
lemma powerfee (t:Team)(x:ℝ): Γ ( NRG t x N G b ) πA ∧ NRG t x N G b∈( PermV πA ).guard:= by
   constructor
   · intro k _; unfold NRG; split; exact ( FeeP πA ).zero_mem; exact memBill (n:=k+2) ( (core_circle G t).actual k x ) ( by obtain ht := style_limit t x G k; exact_mod_cast ht ) -- choose k+2
   intro k _; unfold NRG; split; exact ( actor πA ).guard.zero_mem; exact sendEven ((core_circle G t).actual k x )
-- core circle.P.
end YM.MS.Swirl.Near

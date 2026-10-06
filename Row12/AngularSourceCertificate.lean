import Row12.AngularNormalForm

#print axioms Row12.angular_native_pair_s_hasDerivAt

namespace Row12

set_option maxRecDepth 8000

noncomputable def angularSourceLambda (x : ℂ) : ℂ := (729/15625)*x^3

noncomputable def angularLiteralSource00 (x s : ℂ) : ℂ :=
  -(4281629150390625*s^4*x^8 - 101029148437500000*s^4*x^7 + 704142986572265625*s^4*x^6 - 2295120880371093750*s^4*x^5 + 4038837266601562500*s^4*x^4 - 4024765283203125000*s^4*x^3 + 2254116210937500000*s^4*x^2 - 658984375000000000*s^4*x + 78125000000000000*s^4 - 4144617017578125*s^3*x^8 + 101312860429687500*s^3*x^7 - 708134945009765625*s^3*x^6 + 2303857261933593750*s^3*x^5 - 4046438610351562500*s^3*x^4 + 4027707861328125000*s^3*x^3 - 2254538085937500000*s^3*x^2 + 658984375000000000*s^3*x - 78125000000000000*s^3 - 269639877375000*s^2*x^8 + 1507100245875000*s^2*x^7 - 2855634243750000*s^2*x^6 + 2382804843750000*s^2*x^5 - 856195312500000*s^2*x^4 + 63281250000000*s^2*x^3 - 2390771837619000*s*x^11 + 23597459134582500*s*x^10 - 94854059552047500*s*x^9 + 202088188659780000*s*x^8 - 249649369866000000*s*x^7 + 183925234710000000*s*x^6 - 79544743875000000*s*x^5 + 18625950000000000*s*x^4 - 1822500000000000*s*x^3 + 167763144669714*x^14 - 1650518211194964*x^13 + 6625232066771298*x^12 - 14114782198000080*x^11 + 17446623198311376*x^10 - 12862112285687040*x^9 + 5565481860276000*x^8 - 1303518484800000*x^7 + 127545840000000*x^6)/(2025000000*s^3*x^2*(9*x - 25)*(99*x - 50)^3)

noncomputable def angularLiteralSource01 (x s : ℂ) : ℂ :=
  -(28258752392578125*s^4*x^8 - 505777174365234375*s^4*x^7 + 3183632024853515625*s^4*x^6 - 9855286109033203125*s^4*x^5 + 16854230046972656250*s^4*x^4 - 16560685327148437500*s^4*x^3 + 9237139892578125000*s^4*x^2 - 2701835937500000000*s^4*x + 320312500000000000*s^4 - 28176545112890625*s^3*x^8 + 509155976598046875*s^3*x^7 - 3202593396866015625*s^3*x^6 + 9890618734283203125*s^3*x^5 - 16884336607910156250*s^3*x^4 + 16572873295898437500*s^3*x^3 - 9239291455078125000*s^3*x^2 + 2701835937500000000*s^3*x - 320312500000000000*s^3 - 79576646737500*s^2*x^8 - 88418496375000*s^2*x^7 + 2068172772187500*s^2*x^6 - 4541339671875000*s^2*x^5 + 3962798437500000*s^2*x^4 - 1518750000000000*s^2*x^3 + 210937500000000*s^2*x^2 - 599291068921875*s*x^11 + 5919494506553250*s*x^10 - 23792197119546375*s*x^9 + 50649518071764000*s*x^8 - 62511584644575000*s*x^7 + 46017476190000000*s*x^6 - 19891106718750000*s*x^5 + 4656487500000000*s*x^4 - 455625000000000*s*x^3 + 27960524111619*x^14 - 275086368532494*x^13 + 1104205344461883*x^12 - 2352463699666680*x^11 + 2907770533051896*x^10 - 2143685380947840*x^9 + 927580310046000*x^8 - 217253080800000*x^7 + 21257640000000*x^6)/(1012500000*s^3*x^2*(9*x - 25)*(99*x - 50)^3)

noncomputable def angularLiteralSource02 (x s : ℂ) : ℂ :=
  -(-15625*s + 729*x^3)*(2192194125*s^2*x^8 - 51726924000*s^2*x^7 + 360521209125*s^2*x^6 - 1175101890750*s^2*x^5 + 2067884680500*s^2*x^4 - 2060679825000*s^2*x^3 + 1154107500000*s^2*x^2 - 337400000000*s^2*x + 40000000000*s^2 - 2192194125*s*x^8 + 52344104148*s*x^7 - 363697494201*s*x^6 + 1180773569070*s*x^5 - 2072341786500*s*x^4 + 2062283625000*s*x^3 - 1154323500000*s*x^2 + 337400000000*s*x - 40000000000*s - 85739148*x^7 + 400982076*x^6 - 593464320*x^5 + 336798000*x^4 - 64800000*x^3)/(52488*s*x^5*(9*x - 25)*(99*x - 50)^3)

noncomputable def angularLiteralSource10 (x s : ℂ) : ℂ :=
  -(93032929687500*s^3*x^5 - 497115351562500*s^3*x^4 + 915635390625000*s^3*x^3 - 745558593750000*s^3*x^2 + 278320312500000*s^3*x - 39062500000000*s^3 - 167459273437500*s^2*x^6 + 889942241250000*s^2*x^5 - 1524889167187500*s^2*x^4 + 1019669765625000*s^2*x^3 - 164847656250000*s^2*x^2 - 109570312500000*s^2*x + 39062500000000*s^2 - 1692753114083625*s*x^9 + 16754662683753750*s*x^8 - 67480580912968125*s*x^7 + 144122153519925000*s*x^6 - 178933830121125000*s*x^5 + 133031043765000000*s*x^4 - 58293019406250000*s*x^3 + 13874456250000000*s*x^2 - 1383750000000000*s*x + 117019971281961*x^12 - 1151287394228586*x^11 + 4621303849044177*x^10 - 9862542726046920*x^9 + 12263400008626824*x^8 - 9149455426080960*x^7 + 4029155725194000*x^6 - 964750435200000*x^5 + 96840360000000*x^4)/(187500000*s^3*(9*x - 25)*(99*x - 50)^3)

noncomputable def angularLiteralSource11 (x s : ℂ) : ℂ :=
  -(1691507812500*s^3*x^4 - 8184164062500*s^3*x^3 + 12514500000000*s^3*x^2 - 8008593750000*s^3*x + 1796875000000*s^3 - 461320312500*s^2*x^5 - 986200312500*s^2*x^4 + 12776180625000*s^2*x^3 - 22920468750000*s^2*x^2 + 15982031250000*s^2*x - 4609375000000*s^2 - 1996291686375*s*x^8 + 18804242623500*s*x^7 - 70386902535375*s*x^6 + 135272652608250*s*x^5 - 144770597325000*s*x^4 + 86707715625000*s*x^3 - 27137531250000*s*x^2 + 3459375000000*s*x + 94143178827*x^11 - 878669669052*x^10 + 3274090552539*x^9 - 6288695470890*x^8 + 6732851538168*x^7 - 4041778866120*x^6 + 1267545834000*x^5 - 161400600000*x^4)/(46875000*s^3*(9*x - 25)*(99*x - 50)^2)

noncomputable def angularLiteralSource12 (x s : ℂ) : ℂ :=
  -(-15625*s + 729*x^3)*(s - 1)*(30375*s*x^3 - 131625*s*x^2 + 158250*s*x - 50000*s + 972*x^3 + 540*x^2)/(30375*s^2*x^3*(9*x - 25)*(99*x - 50))

noncomputable def angularLiteralSource20 (x s : ℂ) : ℂ :=
  -81*x*(s - 1)*(-1644145593750*s*x^8 + 16208950500000*s*x^7 - 65103367781250*s*x^6 + 138647872125000*s*x^5 - 171241371000000*s*x^4 + 126150007500000*s*x^3 - 54557437500000*s*x^2 + 12775000000000*s*x - 1250000000000*s + 115063885233*x^11 - 1132042668858*x^10 + 4544054915481*x^9 - 9680920574760*x^8 + 11966133880872*x^7 - 8821750538880*x^6 + 3817202922000*x^5 - 894045600000*x^4 + 87480000000*x^3)/(7812500*s^4*(9*x - 25)*(99*x - 50)^3)

noncomputable def angularLiteralSource21 (x s : ℂ) : ℂ :=
  -3*(-15625*s + 729*x^3)*(s - 1)*(12028500*s*x^4 - 58198500*s*x^3 + 88992000*s*x^2 - 51450000*s*x + 10000000*s + 14348907*x^8 - 133923132*x^7 + 499023099*x^6 - 955215990*x^5 + 1009790388*x^4 - 590110920*x^3 + 177984000*x^2 - 21600000*x)/(7812500*s^4*(9*x - 25)*(99*x - 50)^2)

noncomputable def angularLiteralSource22 (_x _s : ℂ) : ℂ :=
  0

noncomputable def angularLiteralG0 (x : ℂ) : ℂ :=
  -(49911735537576000*x^10 - 358366114625568750*x^9 + 1024896781084880250*x^8 - 1504649505484526625*x^7 + 452996231267528739*x^6 - 967095462947044050*x^5 + 4568259094506607500*x^4 - 6390265799696625000*x^3 + 4776671745037500000*x^2 - 1620026581250000000*x + 203665000000000000)/(884458575000*x^2*(99*x - 50)^3)

noncomputable def angularLiteralG1 (x : ℂ) : ℂ :=
  -(424991536633320525*x^10 - 3059269893497952675*x^9 + 8776295385209831250*x^8 - 17980716578328028350*x^7 + 40033847500084452231*x^6 - 72681314187914929575*x^5 + 72991314248116398750*x^4 - 42274489174403062500*x^3 + 20412363692634375000*x^2 - 6742838987500000000*x + 835026500000000000)/(442229287500*x^2*(99*x - 50)^3)

noncomputable def angularLiteralG2 (x : ℂ) : ℂ :=
  -(16254637002555354315*x^13 - 117331289817565846140*x^12 + 337708827799074815355*x^11 - 712568763360020254725*x^10 + 1748175772637166704388*x^9 - 3284853027606881257275*x^8 + 3704502474256540713750*x^7 - 9155313050168474437500*x^6 + 35764645331938415625000*x^5 - 76328567295533437500000*x^4 + 86614239637406250000000*x^3 - 52943748309375000000000*x^2 + 16445948750000000000000*x - 2036650000000000000000)/(1990031793750*x^5*(99*x - 50)^3)

noncomputable def angularLiteralG3 (x : ℂ) : ℂ :=
  -(1985653292967065304*x^13 - 14368114735064950374*x^12 + 41475305233234945818*x^11 - 88343270723508495705*x^10 + 221167038990204750141*x^9 - 423533970403323140880*x^8 + 474160356450500328000*x^7 - 968138785177596900000*x^6 + 3581908522999976250000*x^5 - 7627707731215687500000*x^4 + 8660787001453125000000*x^3 - 5294374830937500000000*x^2 + 1644594875000000000000*x - 203665000000000000000)/(61420734375000*x^2*(99*x - 50)^3)

noncomputable def angularLiteralG4 (x : ℂ) : ℂ :=
  -(36543294297940253472*x^13 - 263435458016134499112*x^12 + 757044868395948363864*x^11 - 1569822791226846121485*x^10 + 3723903857070844049628*x^9 - 6706460023297782552765*x^8 + 7104436804434687747750*x^7 - 18032895993731205825000*x^6 + 72792768566568622500000*x^5 - 156236863530002062500000*x^4 + 177487785902109375000000*x^3 - 108534684034218750000000*x^2 + 33714194937500000000000*x - 4175132500000000000000)/(153551835937500*x^2*(99*x - 50)^3)

noncomputable def angularLiteralG5 (x : ℂ) : ℂ :=
  -(14697320943081344436*x^13 - 106064566372879052661*x^12 + 305192775314146313547*x^11 - 642442623371264688075*x^10 + 1566716945575890250404*x^9 - 2892773628120033493245*x^8 + 3118878132004496822625*x^7 - 7639960648920801665625*x^6 + 30095841001386345468750*x^5 - 64187382415999992187500*x^4 + 72733992740694140625000*x^3 - 44373556405664062500000*x^2 + 13773482078125000000000*x - 1705694375000000000000)/(38387958984375*x^2*(99*x - 50)^3)

noncomputable def angularPrimitiveCoefficients00 (x : ℂ) : Fin 6 → ℂ :=
  ![109910779164514140813*x^14 - 1081344433396331041938*x^13 + 4340550602089516355541*x^12 - 9247363073539643412360*x^11 + 11430233698178090387592*x^10 - 8426670743473149847680*x^9 + 3646250485428192642000*x^8 - 854006001149901600000*x^7 + 83562231032280000000*x^6,
    -2349351416685771122625*x^11 + 23188259573408150471250*x^10 - 93209401260517742825625*x^9 + 198582351107101661700000*x^8 - 245330184898269095625000*x^7 + 180747572597246655000000*x^6 - 78170726669566781250000*x^5 + 18304312438912500000000*x^4 - 1791028614375000000000*x^3,
    -103256505922161091500*x^11 + 690600044800980814500*x^10 - 1706005613445410277000*x^9 + 3687620197131236866500*x^8 - 9346401837058411125000*x^7 + 11562838970874128437500*x^6 - 2668141265555390625000*x^5 - 5222379701601562500000*x^4 + 4214279991796875000000*x^3 - 570734226562500000000*x^2,
    -183048092977187109375*x^11 + 1835008506910743750000*x^10 - 7520955096108540234375*x^9 + 20179327537330400390625*x^8 - 119296488994596998437500*x^7 + 714201357849115833984375*x^6 - 2289710363882834003906250*x^5 + 4017035571644874023437500*x^4 - 3998847306311279296875000*x^3 + 2238551413731445312500000*x^2 - 654315470703125000000000*x + 77571484375000000000000,
    -2817821494825927734375*x^8 + 66489202140539062500000*x^7 - 463409878179952880859375*x^6 + 1510462658668943847656250*x^5 - 2658035543058553710937500*x^4 + 2648774503416357421875000*x^3 - 1483476706625976562500000*x^2 + 433690137890625000000000*x - 51415546875000000000000,
    0]

noncomputable def angularPrimitiveCoefficients01 (x : ℂ) : Fin 6 → ℂ :=
  ![-7832168540039844*x^11 + 98653678479087732*x^10 - 385613433798504912*x^9 + 631167886596671424*x^8 - 486050026425163200*x^7 + 175444511041800000*x^6 - 24116083992000000*x^5,
    -1972836231141147372*x^11 + 12928334698009562832*x^10 - 31120192362464625420*x^9 + 54083163447068956200*x^8 - 104939595820651672080*x^7 + 86898194863177698000*x^6 + 71828315904044700000*x^5 - 166342457103322500000*x^4 + 97731236728125000000*x^3 - 15403362975000000000*x^2,
    -11864807139579829875*x^11 + 118823373894445347375*x^10 - 486418907634935565375*x^9 + 1472397647104596982500*x^8 - 7019110365455073823875*x^7 + 31790461428512818081875*x^6 - 87075009626048974546875*x^5 + 139583722475345646093750*x^4 - 132727199597170664062500*x^3 + 73308697018979296875000*x^2 - 21461547439062500000000*x + 2544344687500000000000,
    -178399915267883203125*x^8 + 2916239199070222265625*x^7 - 17582510028016016015625*x^6 + 53119759183391471484375*x^5 - 89552990835629655468750*x^4 + 87354879185038007812500*x^3 - 48619991715216796875000*x^2 + 14225036522812500000000*x - 1686429937500000000000,
    0,
    0]

noncomputable def angularPrimitiveCoefficients02 (x : ℂ) : Fin 6 → ℂ :=
  ![634405651743227364*x^14 - 7990947956806106292*x^13 + 31234688137678897872*x^12 - 51124598814330385344*x^11 + 39370052140438219200*x^10 - 14211005394385800000*x^9 + 1953402803352000000*x^8,
    -117012597988195269360*x^14 + 762364773289111048056*x^13 - 1821217631579260498584*x^12 + 2285164099071749924028*x^11 + 904049609534033983020*x^10 - 15298632320694029307000*x^9 + 30702220594183838700000*x^8 - 25797698528762160000000*x^7 + 9990590212102500000000*x^6 - 1373277005100000000000*x^5,
    -3921404223823161287850*x^14 + 39244905724755562991100*x^13 - 160518824653587998265450*x^12 + 414943637468263969804875*x^11 - 1184875292689912385089650*x^10 + 3774729636836667996478875*x^9 - 8727058052066614544212500*x^8 + 13984840339365107835000000*x^7 - 21714877254465723796875000*x^6 + 40181867512380766406250000*x^5 - 61435488937776679687500000*x^4 + 59411390099660156250000000*x^3 - 33082626334570312500000000*x^2 + 9663267796875000000000000*x - 1145615625000000000000000,
    -8706980822017654687500*x^11 + 176964429535400482031250*x^10 - 1172977445257947014062500*x^9 + 3518421756701949801562500*x^8 - 1405118803557354932812500*x^7 - 28842666763150885605468750*x^6 + 110891932719001883789062500*x^5 - 199882346806500380859375000*x^4 + 199839025485821777343750000*x^3 - 111927570686572265625000000*x^2 + 32715773535156250000000000*x - 3878574218750000000000000,
    140891074741296386718750*x^8 - 3324460107026953125000000*x^7 + 23170493908997644042968750*x^6 - 75523132933447192382812500*x^5 + 132901777152927685546875000*x^4 - 132438725170817871093750000*x^3 + 74173835331298828125000000*x^2 - 21684506894531250000000000*x + 2570777343750000000000000,
    0]

noncomputable def angularPrimitiveCoefficients10 (x : ℂ) : Fin 6 → ℂ :=
  ![219821558329028281626*x^14 - 2162688866792662083876*x^13 + 8681101204179032711082*x^12 - 18544982561877875823720*x^11 + 23137131498025180820184*x^10 - 17377339347191969505360*x^9 + 7726063606567370064000*x^8 - 1871654704738018200000*x^7 + 190336192906860000000*x^6,
    -4611763345241130828750*x^11 + 45855658939823515282500*x^10 - 185295080766945187788750*x^9 + 397110048264648408690000*x^8 - 496038795161164880625000*x^7 + 372645037292731953750000*x^6 - 165671700605160750000000*x^5 + 40116055914309375000000*x^4 - 4079565177187500000000*x^3,
    -137002516051468567500*x^11 + 897801020695108530000*x^10 - 2161124469615598987500*x^9 + 102016687493345625000*x^8 + 13208968045176178275000*x^7 - 32985811025186394375000*x^6 + 36819879804238781250000*x^5 - 17635998812463281250000*x^4 + 1301866307929687500000*x^3 + 128026335937500000000*x^2,
    -307045040478157265625*x^11 + 3048652692806063203125*x^10 - 12348466026943303828125*x^9 + 25637389885939251093750*x^8 - 19314167800466453906250*x^7 - 59155341512837586328125*x^6 + 250585368329408730468750*x^5 - 451257960528149414062500*x^4 + 450283750010595703125000*x^3 - 252156880561523437500000*x^2 + 73727830859375000000000*x - 8740703125000000000000,
    228472013093994140625*x^8 - 5391016389773437500000*x^7 + 37573773906482666015625*x^6 - 122469945297481933593750*x^5 + 215516395383125976562500*x^4 - 214765500277001953125000*x^3 + 120281895131835937500000*x^2 - 35164065234375000000000*x + 4168828125000000000000,
    0]

noncomputable def angularPrimitiveCoefficients11 (x : ℂ) : Fin 6 → ℂ :=
  ![484724208533577012*x^11 - 2968347925112025456*x^10 + 6493727216926505556*x^9 - 6846281587248215112*x^8 + 3071276143304569200*x^7 - 542772663713280000*x^6 - 54931080204000000*x^5 - 143282289150000000*x^4,
    -3366091990319346288*x^11 + 21693515809327037676*x^10 - 51076450365331963572*x^9 + 33677950428489731364*x^8 + 180861528107869949340*x^7 - 680990411510988579000*x^6 + 996842261837822400000*x^5 - 679569036072176250000*x^4 + 232659699772500000000*x^3 - 48352316512500000000*x^2 + 3071036718750000000*x,
    -22338175481008299000*x^11 + 222465914820584724375*x^10 - 904467548695943533500*x^9 + 2135928595253733172125*x^8 - 3819876255203204377125*x^7 + 5011066201656382683750*x^6 - 1150164051633884671875*x^5 - 8791078571099163281250*x^4 + 13583085851103398437500*x^3 - 8360190125396484375000*x^2 + 2418272852187500000000*x - 286695062500000000000,
    14779930354702734375*x^8 - 239146809521902734375*x^7 + 1434340633599882421875*x^6 - 4320114542965044140625*x^5 + 7269736499355438281250*x^4 - 7084569042389179687500*x^3 + 3942022070314453125000*x^2 - 1153381339687500000000*x + 136737562500000000000,
    0,
    0]

noncomputable def angularPrimitiveCoefficients12 (x : ℂ) : Fin 6 → ℂ :=
  ![4683636786943826712*x^13 - 17749829957695751916*x^12 + 24948612522255718296*x^11 - 18192716184987135792*x^10 + 6134140596512728800*x^9 + 824770072526400000*x^8,
    -25791331002351206292*x^13 + 95108158627669291104*x^12 - 130114137005972447328*x^11 - 169703542607407472664*x^10 + 1670896710381920881860*x^9 - 3323879477249225895000*x^8 + 2785006302255777600000*x^7 - 1050904135851570000000*x^6 + 125120793798000000000*x^5,
    -913802383568714589675*x^13 + 6588873179217602579925*x^12 - 18939521426215195306350*x^11 + 39702535231262404192875*x^10 - 92600751012743297929950*x^9 + 157280891792592231806625*x^8 - 146401299334492932318750*x^7 + 388786127899365945000000*x^6 - 1738879898456003062500000*x^5 + 3848000785387713281250000*x^4 - 4416672497548007812500000*x^3 + 2710306433871093750000000*x^2 - 842854873437500000000000*x + 104378312500000000000000,
    63935869152336328125*x^10 - 1296867562755648046875*x^9 + 6601736846590291406250*x^8 - 12149818040766016406250*x^7 - 37934457926780805468750*x^6 + 272173165418344570312500*x^5 - 633945529828037109375000*x^4 + 736436184650332031250000*x^3 - 453495313154296875000000*x^2 + 141162355468750000000000*x - 17481406250000000000000,
    -1269288961633300781250*x^7 + 26424288383093261718750*x^6 - 135342387305200195312500*x^5 + 304437509138232421875000*x^4 - 351653560077832031250000*x^3 + 216326223544921875000000*x^2 - 67326574218750000000000*x + 8337656250000000000000,
    0]

noncomputable def angularPrimitiveCoefficients20 (x : ℂ) : Fin 6 → ℂ :=
  ![-219821558329028281626*x^14 + 2162688866792662083876*x^13 - 8681101204179032711082*x^12 + 18494726147079286824720*x^11 - 22860467396356180775184*x^10 + 16853341486946299695360*x^9 - 7292500970856385284000*x^8 + 1708012002299803200000*x^7 - 167124462064560000000*x^6,
    219821558329028281626*x^14 - 2162688866792662083876*x^13 + 8681101204179032711082*x^12 - 13796023313707744579470*x^11 - 23516051750460120167316*x^10 + 169565461034089185955890*x^9 - 389892882895527427416000*x^8 + 488951313266350484550000*x^7 - 361322217799718175000000*x^6 + 156341453339133562500000*x^5 - 36608624877825000000000*x^4 + 3582057228750000000000*x^3,
    -4598383390651896095250*x^11 + 45722914231444978027500*x^10 - 184857401945264514716250*x^9 + 396274500970419376305000*x^8 - 497211863510089277550000*x^7 + 385256782693119211875000*x^6 - 191090838161504531250000*x^5 + 61368180481420312500000*x^4 - 12134994199453125000000*x^3 + 1141468453125000000000*x^2,
    -100319442719646150000*x^11 + 653604915371322915000*x^10 - 1561400575770970935000*x^9 + 1114659095524181707500*x^8 + 12655665847852780252500*x^7 - 56894520043355494500000*x^6 + 91171560700814343750000*x^5 - 81013984551812812500000*x^4 + 45263994643054687500000*x^3 - 9174343303125000000000*x^2 + 383879589843750000000*x,
    -280753512398865000000*x^11 + 2795680262543449218750*x^10 - 11364514934626963125000*x^9 + 24350046810939968906250*x^8 - 33958385393747180625000*x^7 + 58169649006812165625000*x^6 - 138052814992751250000000*x^5 + 235417520884218750000000*x^4 - 235016239450781250000000*x^3 + 131874985429687500000000*x^2 - 38563765625000000000000*x + 4571875000000000000000,
    -76157337697998046875*x^8 + 1797005463257812500000*x^7 - 12524591302160888671875*x^6 + 40823315099160644531250*x^5 - 71838798461041992187500*x^4 + 71588500092333984375000*x^3 - 40093965043945312500000*x^2 + 11721355078125000000000*x - 1389609375000000000000]

noncomputable def angularPrimitiveCoefficients21 (x : ℂ) : Fin 6 → ℂ :=
  ![1740481897786632*x^10 - 17088367723723296*x^9 + 38224186055991936*x^8 - 34081235754838272*x^7 + 13341017664374400*x^6 - 1929286719360000*x^5,
    316671011958401100*x^10 - 1157086430148737088*x^9 + 1568123184388112352*x^8 - 6358856678758584*x^7 - 10693431293252067360*x^6 + 24670030441296240000*x^5 - 21768279010077600000*x^4 + 8521140397770000000*x^3 - 1232269038000000000*x^2,
    -318411493856187732*x^10 + 1174174797872460384*x^9 - 1606347370444104288*x^8 + 179876275564841856*x^7 + 20194165096715790180*x^6 - 46142181468772389000*x^5 + 46025769389049450000*x^4 - 24716108729812500000*x^3 + 3614334223500000000*x^2,
    -2124957683166602625*x^10 + 15296349467489763375*x^9 - 43881476926049156250*x^8 + 90851258819810459250*x^7 - 220137251027067155250*x^6 + 423922759758237735000*x^5 - 463219879380489000000*x^4 + 306119178236025000000*x^3 - 151618254263437500000*x^2 + 48436272500000000000*x - 5998300000000000000,
    -1087112111301562500*x^7 + 10453938705516796875*x^6 - 39042108504467578125*x^5 + 74005817760935156250*x^4 - 78551764031967187500*x^3 + 47174370614765625000*x^2 - 14722077562500000000*x + 1823167500000000000,
    0]

noncomputable def angularPrimitiveCoefficients22 (x : ℂ) : Fin 6 → ℂ :=
  ![-140979033720717192*x^13 + 1384157785621586976*x^12 - 3096159070535346816*x^11 + 2760580096141900032*x^10 - 1080622430814326400*x^9 + 156272224268160000*x^8,
    21389652282848813964*x^13 - 80126644241216713140*x^12 + 111357842624787422664*x^11 + 18460918389887365392*x^10 - 958062123285212705760*x^9 + 2196063181374622560000*x^8 - 1940737036039401600000*x^7 + 759696839221320000000*x^6 - 109862160408000000000*x^5,
    -21248673249128096772*x^13 + 78742486455595126164*x^12 - 108261683554252075848*x^11 - 418251472881049731924*x^10 + 2664811699412681718900*x^9 - 4720883563188175383000*x^8 + 1924180699608592425000*x^7 + 18821992559137267500000*x^6 - 45481157336364750000000*x^5 + 40328537036287500000000*x^4 - 15786508706718750000000*x^3 + 2282936906250000000000*x^2,
    -731458665114990944175*x^13 + 5279908041790463076300*x^12 - 15196897250958366690975*x^11 + 32555396329969731538500*x^10 - 81284363721470065759200*x^9 + 153792663565239686162250*x^8 - 172318893140339649506250*x^7 + 379661268830830983281250*x^6 - 1465829579163129117187500*x^5 + 3164479439921469140625000*x^4 - 3614048178640839843750000*x^3 + 2215125388587890625000000*x^2 - 688674103906250000000000*x + 85284718750000000000000,
    -92772004373799609375*x^10 + 910784999100909375000*x^9 - 3449613213340744921875*x^8 + 5209741814681692968750*x^7 + 21554225156089532812500*x^6 - 143102570379060234375000*x^5 + 331456721053992187500000*x^4 - 385023949695000000000000*x^3 + 237169089609375000000000*x^2 - 73835781250000000000000*x + 9143750000000000000000,
    423096320544433593750*x^7 - 8808096127697753906250*x^6 + 45114129101733398437500*x^5 - 101479169712744140625000*x^4 + 117217853359277343750000*x^3 - 72108741181640625000000*x^2 + 22442191406250000000000*x - 2779218750000000000000]

noncomputable def angularLiteralSource (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![angularLiteralSource00 x s, angularLiteralSource01 x s, angularLiteralSource02 x s;
    angularLiteralSource10 x s, angularLiteralSource11 x s, angularLiteralSource12 x s;
    angularLiteralSource20 x s, angularLiteralSource21 x s, angularLiteralSource22 x s]

noncomputable def angularSourceCoordinates (x : ℂ) : Fin 6 → ℂ :=
  ![angularLiteralG0 x, angularLiteralG1 x, angularLiteralG2 x, angularLiteralG3 x, angularLiteralG4 x, angularLiteralG5 x]

noncomputable def angularPrimitiveCoefficients (x : ℂ) : Matrix (Fin 3) (Fin 3) (Fin 6 → ℂ) :=
  !![angularPrimitiveCoefficients00 x, angularPrimitiveCoefficients01 x, angularPrimitiveCoefficients02 x;
    angularPrimitiveCoefficients10 x, angularPrimitiveCoefficients11 x, angularPrimitiveCoefficients12 x;
    angularPrimitiveCoefficients20 x, angularPrimitiveCoefficients21 x, angularPrimitiveCoefficients22 x]

noncomputable def angularPrimitiveScale (x : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3980063587500000*x^2*(9*x - 25)*(99*x - 50)^3, 15920254350000*x^2*(9*x - 25)*(99*x - 50)^3, 644770301175000*x^5*(9*x - 25)*(99*x - 50)^3;
    1105573218750000*x^2*(9*x - 25)*(99*x - 50)^3, 4422292875000*x^2*(9*x - 25)*(99*x - 50)^3, 179102861437500*x^5*(99*x - 50)^3;
    552786609375000*x^2*(9*x - 25)*(99*x - 50)^3, 2211146437500*x^2*(99*x - 50)^3, 89551430718750*x^5*(99*x - 50)^3]

def angularPrimitivePole : Matrix (Fin 3) (Fin 3) ℕ :=
  !![2, 1, 1;
    2, 1, 1;
    3, 2, 2]

noncomputable def angularSourcePolynomial (c : Fin 6 → ℂ) (s : ℂ) : ℂ :=
  ∑ k : Fin 6, c k * s ^ k.val

noncomputable def angularSourcePolynomialDerivative (c : Fin 6 → ℂ) (s : ℂ) : ℂ :=
  ∑ k : Fin 6, c k * (k.val : ℂ) * s ^ (k.val-1)

noncomputable def angularLiteralPrimitive (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  angularSourcePolynomial (angularPrimitiveCoefficients x i j) s /
    (angularPrimitiveScale x i j * s ^ angularPrimitivePole i j)

noncomputable def angularLiteralPrimitiveDerivative (x s : ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  (s * angularSourcePolynomialDerivative (angularPrimitiveCoefficients x i j) s -
    (angularPrimitivePole i j : ℂ) *
      angularSourcePolynomial (angularPrimitiveCoefficients x i j) s) /
    (angularPrimitiveScale x i j * s ^ (angularPrimitivePole i j+1))

theorem angular_source_polynomial_hasDerivAt (c : Fin 6 → ℂ) (s : ℂ) :
    HasDerivAt (angularSourcePolynomial c) (angularSourcePolynomialDerivative c s) s := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_id s).fun_pow k.val).const_mul (c k))
  have hf : (∑ k : Fin 6, fun z : ℂ => c k * z^k.val) = angularSourcePolynomial c := by
    funext z
    simp [angularSourcePolynomial, Finset.sum_apply]
  change HasDerivAt (∑ k : Fin 6, fun z : ℂ => c k * z^k.val) _ s at h
  rw [hf] at h
  simpa only [angularSourcePolynomialDerivative, id_eq, mul_one, mul_assoc] using h

theorem angular_source_scale_ne_zero (x : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (i j : Fin 3) :
    angularPrimitiveScale x i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [angularPrimitiveScale, hx0, hx25, hx50]

theorem angular_source_laurent_hasDerivAt (c : Fin 6 → ℂ) (d s : ℂ) (p : ℕ)
    (hp : 0 < p) (hd : d ≠ 0) (hs : s ≠ 0) :
    HasDerivAt (fun z => angularSourcePolynomial c z / (d*z^p))
      ((s*angularSourcePolynomialDerivative c s - (p : ℂ)*angularSourcePolynomial c s) /
        (d*s^(p+1))) s := by
  have hden : d*s^p ≠ 0 := mul_ne_zero hd (pow_ne_zero _ hs)
  have hD := ((hasDerivAt_id s).fun_pow p).const_mul d
  have h := (angular_source_polynomial_hasDerivAt c s).fun_div hD hden
  apply h.congr_deriv
  cases p with
  | zero => simp at hp
  | succ p =>
    simp only [id_eq, mul_one, Nat.add_sub_cancel, pow_succ]
    field_simp [hd, hs]

theorem angular_source_primitive_entry_hasDerivAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun z => angularLiteralPrimitive x z i j)
      (angularLiteralPrimitiveDerivative x s i j) s := by
  have hp : 0 < angularPrimitivePole i j := by
    fin_cases i <;> fin_cases j <;> simp [angularPrimitivePole]
  exact angular_source_laurent_hasDerivAt (angularPrimitiveCoefficients x i j)
    (angularPrimitiveScale x i j) s (angularPrimitivePole i j) hp
    (angular_source_scale_ne_zero x hx0 hx25 hx50 i j) hs0

theorem angular_source_first_connection (s : ℂ) (hs1 : s ≠ 1) :
    nativeEulerConnection s =
      !![0, 1, 0; 0, 0, 1;
        -5*s/(72*(s-1)), -23*s/(36*(s-1)), -3*s/(2*(s-1))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeEulerConnection] <;>
    field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm] <;> ring

theorem angular_source_second_connection (lambda s : ℂ)
    (hs0 : s ≠ 0) (hsl : s ≠ lambda) :
    nativeEulerConnection (lambda/s) =
      !![0, 1, 0; 0, 0, 1;
        5*lambda/(72*(s-lambda)), 23*lambda/(36*(s-lambda)),
        3*lambda/(2*(s-lambda))] := by
  have hb1 : lambda/s ≠ 1 := by
    intro h
    exact hsl ((div_eq_one_iff_eq hs0).1 h).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeEulerConnection] <;>
    field_simp [hs0, sub_ne_zero.mpr hsl, sub_ne_zero.mpr hb1.symm]

theorem angular_source_cons_val_five {α : Type*} (a : α) (v : Fin 5 → α) :
    Matrix.vecCons a v (5 : Fin 6) =
      Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail v)))) :=
  rfl

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_00 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 0 0 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 0 0 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource00, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG0, angularLiteralG3, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients00, angularPrimitiveCoefficients02, angularPrimitiveCoefficients20, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_01 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 0 1 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 0 1 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource01, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG1, angularLiteralG3, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients00, angularPrimitiveCoefficients01, angularPrimitiveCoefficients02, angularPrimitiveCoefficients21, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_02 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 0 2 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 0 2 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource02, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG2, angularLiteralG3, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients01, angularPrimitiveCoefficients02, angularPrimitiveCoefficients22, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_10 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 1 0 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 1 0 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource10, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG0, angularLiteralG4, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients00, angularPrimitiveCoefficients10, angularPrimitiveCoefficients12, angularPrimitiveCoefficients20, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_11 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 1 1 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 1 1 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource11, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG1, angularLiteralG4, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients01, angularPrimitiveCoefficients10, angularPrimitiveCoefficients11, angularPrimitiveCoefficients12, angularPrimitiveCoefficients21, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_12 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 1 2 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 1 2 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource12, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG2, angularLiteralG4, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients02, angularPrimitiveCoefficients11, angularPrimitiveCoefficients12, angularPrimitiveCoefficients22, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_20 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 2 0 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 2 0 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource20, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG0, angularLiteralG5, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients10, angularPrimitiveCoefficients20, angularPrimitiveCoefficients22, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_21 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 2 1 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 2 1 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource21, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG1, angularLiteralG5, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients11, angularPrimitiveCoefficients20, angularPrimitiveCoefficients21, angularPrimitiveCoefficients22, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

set_option maxHeartbeats 2000000 in
theorem angular_source_identity_22 (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s 2 2 =
      (angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s) 2 2 := by
  have hsd : s-angularSourceLambda x ≠ 0 := sub_ne_zero.mpr hsl
  have hsc : s-1 ≠ 0 := sub_ne_zero.mpr hs1
  let d : ℂ := x^5*(9*x-25)*(99*x-50)^3*s^4*(s-1)*(s-angularSourceLambda x)
  have hd : d ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (pow_ne_zero 5 hx0) hx25) (pow_ne_zero 3 hx50))
      (pow_ne_zero 4 hs0)) (sub_ne_zero.mpr hs1)) hsd
  apply mul_left_cancel₀ hd
  dsimp only [d]
  simp only [angularRowSAction, angular_source_first_connection s hs1,
    angular_source_second_connection (angularSourceLambda x) s hs0 hsl]
  generalize hl : angularSourceLambda x = l at hsd ⊢
  simp only [angularLiteralSource, angularLiteralSource22, angularNFRow, angularNFFirst, angularNFSecond, angularNFWeight, angularSourceCoordinates, angularLiteralG2, angularLiteralG5, angularLiteralPrimitiveDerivative, angularLiteralPrimitive, angularPrimitiveCoefficients, angularPrimitiveCoefficients12, angularPrimitiveCoefficients21, angularPrimitiveCoefficients22, angularSourcePolynomial, angularSourcePolynomialDerivative, angularPrimitiveScale, angularPrimitivePole, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, add_zero, zero_add]
  norm_num only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    angular_source_cons_val_five, Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_zero]
  generalize he : 99*x-50 = e at hx50 ⊢
  generalize hf : 9*x-25 = f at hx25 ⊢
  generalize hc : s-1 = c at hsc ⊢
  generalize ht : s-l = t at hsd ⊢
  simp only [mul_add, mul_sub]
  norm_num
  field_simp [hx0, hx25, hx50, hs0, hsc, hsd]
  subst e f c t l
  simp only [angularSourceLambda]
  ring

theorem angular_source_identity (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x) :
    angularLiteralSource x s =
      angularNFRow (angularSourceCoordinates x) (angularSourceLambda x) s +
        angularLiteralPrimitiveDerivative x s +
        angularRowSAction (angularLiteralPrimitive x s) (angularSourceLambda x) s := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact angular_source_identity_00 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_01 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_02 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_10 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_11 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_12 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_20 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_21 x s hx0 hx25 hx50 hs0 hs1 hsl
  · exact angular_source_identity_22 x s hx0 hx25 hx50 hs0 hs1 hsl

theorem angular_source_lambda_ne_zero (x : ℂ) (hx0 : x ≠ 0) :
    angularSourceLambda x ≠ 0 := by
  simp [angularSourceLambda, hx0]

noncomputable def angularSourceIntegrand (x s : ℂ) : ℂ :=
  angularTensorPair (angularLiteralSource x s) (nativeState s)
    (nativeState ((angularSourceLambda x)/s))

noncomputable def angularSourcePrimitivePair (x s : ℂ) : ℂ :=
  angularTensorPair (angularLiteralPrimitive x s) (nativeState s)
    (nativeState ((angularSourceLambda x)/s))

theorem angular_source_primitive_pair_hasDerivAt (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0) (hs0 : s ≠ 0)
    (hs : ‖s‖ < 1) (hb : ‖(angularSourceLambda x)/s‖ < 1) :
    HasDerivAt (angularSourcePrimitivePair x)
      (angularTensorPair (angularLiteralPrimitiveDerivative x s)
          (nativeState s) (nativeState ((angularSourceLambda x)/s)) +
        angularTensorPair (angularRowSAction (angularLiteralPrimitive x s)
          (angularSourceLambda x) s) (nativeState s)
          (nativeState ((angularSourceLambda x)/s))) s := by
  change HasDerivAt
    (fun z => angularTensorPair (angularLiteralPrimitive x z) (nativeState z)
      (nativeState ((angularSourceLambda x)/z))) _ s
  exact angular_native_pair_s_hasDerivAt (angularLiteralPrimitive x)
    (angularLiteralPrimitiveDerivative x s) (angularSourceLambda x) s
    (angular_source_lambda_ne_zero x hx0) hs0 hs hb
    (angular_source_primitive_entry_hasDerivAt x s hx0 hx25 hx50 hs0)

theorem angular_source_actual_identity (x s : ℂ) (hx0 : x ≠ 0)
    (hx25 : 9*x-25 ≠ 0) (hx50 : 99*x-50 ≠ 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsl : s ≠ angularSourceLambda x)
    (hs : ‖s‖ < 1) (hb : ‖(angularSourceLambda x)/s‖ < 1) :
    angularSourceIntegrand x s =
      angularNFIntegrand (angularSourceCoordinates x) (angularSourceLambda x) s +
        deriv (angularSourcePrimitivePair x) s := by
  rw [(angular_source_primitive_pair_hasDerivAt x s hx0 hx25 hx50 hs0 hs hb).deriv]
  have h := congrArg (fun R => angularTensorPair R (nativeState s)
    (nativeState ((angularSourceLambda x)/s)))
    (angular_source_identity x s hx0 hx25 hx50 hs0 hs1 hsl)
  rw [angular_tensor_pair_add, angular_tensor_pair_add] at h
  simpa only [angularSourceIntegrand, angularNFIntegrand, add_assoc] using h

end Row12

#print axioms Row12.angular_source_polynomial_hasDerivAt
#print axioms Row12.angular_source_scale_ne_zero
#print axioms Row12.angular_source_laurent_hasDerivAt
#print axioms Row12.angular_source_primitive_entry_hasDerivAt
#print axioms Row12.angular_source_first_connection
#print axioms Row12.angular_source_second_connection
#print axioms Row12.angular_source_cons_val_five
#print axioms Row12.angular_source_identity_00
#print axioms Row12.angular_source_identity_01
#print axioms Row12.angular_source_identity_02
#print axioms Row12.angular_source_identity_10
#print axioms Row12.angular_source_identity_11
#print axioms Row12.angular_source_identity_12
#print axioms Row12.angular_source_identity_20
#print axioms Row12.angular_source_identity_21
#print axioms Row12.angular_source_identity_22
#print axioms Row12.angular_source_identity
#print axioms Row12.angular_source_lambda_ne_zero
#print axioms Row12.angular_source_primitive_pair_hasDerivAt
#print axioms Row12.angular_source_actual_identity

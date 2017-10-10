PROJECT NAME: It's a Small World

DESCRIPTION: Everyone is connected to each other in someway or another. When there are just too many "Facts" and "Rules" to process about who knows who and who likes what, this code takes care of it all.

MOTIVATION: This project is for a high school independent study computer science class in discrete mathematics and functional programming. It comes from the Chapter 5 extended example section of Thomas VanDrunen's Discrete Mathematics and Functional Programming textbook. This project emphasizes table lookups, user-defined data types, and let/case statements in Standard ML.

INSTALLATION: Download ItsASmallWorld.sml and open it using a SML IDE such as Notepad++ or Sublime Text. To execute code online, https://www.tutorialspoint.com/execute_smlnj_online.php would be a good option.

USAGE: Test out this matchmaking, conflict resolver by creating a list of Facts about different people: what they Like (ex. Oatmeal, Chocolate, Cars) and who they Know. Create a list of rules that express conditional statements about people. For example, a Rule may be: if a person x likes Cars, then they will Know Fred. People and things are defined as Const , while any person x is considered a Var, both from the data type atom. Facts feature the words "Likes" or "Knows" followed by a list of 2 Const data types that are connected by the "Likes" or "Knows."

______________________________________________________________________________________________________________________________
EXAMPLE of Creating a Fact List:
val factList = ref [Fact("Knows", [Const("John"), Const("Jane")]),
                    Fact("Knows", [Var("y"), Const("Bill")])];
val factList = 
  ref [Fact("Likes", [Const("Kathy"), Const("Cars")]),
   Fact("Likes", [Const("Maisie"), Const("Cars")]),
   Fact("Likes", [Const("Maisie"), Const("Oatmeal")]),
   Fact("Likes", [Const("Harvey"), Var("x")])];


EXAMPLE of Creating a Rule List:
val ruleList = ref([]: rule list);

val ruleList =
  ref [Rule([Fact("Likes", [Var("x"), Const("Cars")])], 
        Fact("Knows", [Var("x"), Const("Jim")])),
      Rule([Fact("Likes", [Var("x"), Const("Oatmeal")])], 
        Fact("Knows", [Var("x"), Const("Jim")])),



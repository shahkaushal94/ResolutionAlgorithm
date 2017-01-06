import java.util.*;
import java.io.*;

public class Resolution {
	

	public static HashMap<String, ArrayList<String>> kbFinal = new HashMap<String, ArrayList<String>>();

	public static int countForInfinite = 0;
    
	public static void main(String args[]) throws Exception
	{
		
		 FileWriter fw1 = new FileWriter("output.txt");
		 PrintWriter pw1 = new PrintWriter(fw1); 
		
		
		
		ReadFile file = new ReadFile("input.txt");
		String textFile[] = file.OpenFile();
		
		ArrayList<String> q = new ArrayList<String>();
		int nq = Integer.parseInt(textFile[0]);
		for(int i=0 ;i<nq; i++)
		{
			q.add(textFile[i+1]);
		}
		
		int ns = Integer.parseInt(textFile[nq+1]);
		ArrayList<String> s = new ArrayList<String>();
		for(int i=nq+1 ; i<nq+1+ns ; i++)
		{
			s.add(textFile[i+1]);
		}
		
		/*
		System.out.println("------------------Q is ");
		for(String s2: q)
		{
			System.out.println(s2);
		}
		System.out.println();
		
		System.out.println("-----------------S is ");
		for(String s1: s)
		{
			System.out.println(s1);
		}
		*/
		// Removing spaces from s
		

	//	System.out.println("Removing spaces");
		for(int i=0;i<s.size(); i++)
		{
			String sstring = s.get(i);
			sstring = sstring.replaceAll(" ", "");
			//System.out.println(sstring);
			//cleanS.add(sstring);
			s.set(i,sstring);
		}
		
		/*
		System.out.println("-----------------s is ");
		for(String s1: s)
		{
			System.out.println(s1);
		}
		*/
		
		
	//	System.out.println("Replacing => by >");
		for(int i = 0; i<s.size(); i++)
		{
			String sstring = s.get(i);
			for(int j=0; j<sstring.length(); j++)
			{
				if(sstring.charAt(j) == '=')
				{
					sstring = sstring.replaceAll("=", "");
					s.set(i, sstring);
				}
			}
		}
		
		/*
		System.out.println("-----------------s is ---------------------------");
		for(String s1: s)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		// This function converts Predicates into P
		int predicateCounter= 0;
		HashMap<String, String> hm = new HashMap<String, String>();
		HashMap<String, String> hm1 = new HashMap<String, String>();
		ArrayList<String> newS = new ArrayList<String>();
		
		for(int i=0; i<s.size(); i++)
		{
			String sstring = s.get(i);
			
			//System.out.println("The string to convert is "+sstring);
			
			//int startIndex = 0;
			//int endIndex = sstring.length();
			String p = new String();
			
			for(int j=0; j<sstring.length(); j++)
			{
				if(sstring.charAt(j) >= 'A' && sstring.charAt(j) <= 'Z')
				{
					int startIndex = j;
					while(sstring.charAt(j) != ')')
					{
						j++;
					}
					int endIndex = j;
					
					String predicate = sstring.substring(startIndex, endIndex+1);
					predicateCounter++;
					if(predicateCounter < 10)
					{
						if(!hm.containsKey(predicate))
						{
							p = p + "P" + "00"+ predicateCounter ;
							hm.put(predicate, "P" + "00" + predicateCounter);
							hm1.put("P"+"00"+predicateCounter, predicate);			
						}
						else
						{
							p = p+ hm.get(predicate) ;
						}
					}
					else if(predicateCounter < 100)
					{
						if(!hm.containsKey(predicate))
						{
							p =  p + "P" + "0"+ predicateCounter ;
							hm.put(predicate, "P" + "0" + predicateCounter);
							hm1.put("P"+"0"+predicateCounter, predicate);			
						}
						else
						{
							p = p + hm.get(predicate) ;
						}
					}
					else if(predicateCounter < 800)
					{
						if(!hm.containsKey(predicate))
						{
							p = p + "P" + predicateCounter ;
							hm.put(predicate, "P" + predicateCounter);
							hm1.put("P"+predicateCounter, predicate);			
						}
						else
						{
							p =  p + hm.get(predicate) ;
						}
					}
				}
				else
				{
					p = p + sstring.charAt(j);
				}
					
				}
				newS.add(p);	
			}
			
		
		
		
		/*
		System.out.println("-----------------newS is-------------------- ");
		for(String s1: newS)
		{
			System.out.println(s1);
		}
		System.out.println();
		
		*/
		
		
		ArrayList<String> prefixS = new ArrayList<String>();
		prefixS = prefixFunction(newS);
		
		/*
		System.out.println("-----------------prefixS is-------------------------------- ");
		for(String s1: prefixS)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		
				
		
		ArrayList<String> removedImplication = new ArrayList<String>();
		removedImplication = removeImplication(prefixS);
		
		/*
		System.out.println("-----------------removedImplication is-------------------------------- ");
		for(String s1: removedImplication)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		
		ArrayList<String> prefixRemovedImplication = new ArrayList<String>();
		prefixRemovedImplication = prefixFunction(removedImplication);
		
		/*
		System.out.println("-----------------prefixRemovedImplication is-------------------------------- ");
		for(String s1: prefixRemovedImplication)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		
		ArrayList<String> negationInwards = new ArrayList<String>();
		negationInwards = negateInside(prefixRemovedImplication);
		
		/*
		System.out.println("-----------------negationInwards is-------------------------------- ");
		for(String s1: negationInwards)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		
		ArrayList<String> prefixNegationInwards = new ArrayList<String>();
		prefixNegationInwards = prefixFunction(negationInwards);
		
		/*
		System.out.println("-----------------prefixNegationInwards is-------------------------------- ");
		for(String s1: prefixNegationInwards)
		{
			System.out.println(s1);
		}
		System.out.println();
		*/
		
		ArrayList<String> distributivityArray = new ArrayList<String>();
		distributivityArray = distributivity(prefixNegationInwards);
		
		/*
		System.out.println("-----------------distributivityArray is ");
		for(String s1: distributivityArray)
		{
			System.out.println(s1);
		}
		*/
		
		//Adding into kn by splitting on &
		ArrayList<String> kb = new ArrayList<String>();
		kb = splitAnd(distributivityArray);
		//System.out.println("The knowledge base is " + kb);
		
		//displayHashMap(hm);
		//displayHashMap(hm1);
		
		ArrayList<String> standardizeVar = new ArrayList<String>();
		standardizeVar = standardizingVar(kb, hm1);
		
		/*
		System.out.println("The standardizeVar is =====================");
		
		for(String s1: standardizeVar)
		{
			System.out.println(s1);
		}
		*/
		kbFinal = makeHashMap(standardizeVar);
		
		//displayHashMap(kbfinal);
		/*
		System.out.println("Display KB before query ");
		displayKbHashMap(kbFinal);
		*/
		
		//Now solving queries
		
		for(int i=0; i<q.size(); i++)
		{
			Stack<String> currentQueryStack = new Stack<String>();
			String qString = q.get(i);
			
			qString = qString.replaceAll(" ", "");
			
			
			
			if(qString.contains("~"))
			{
				qString = qString.substring(1);
			}
			else
			{
				qString = '~' + qString;
			}
			currentQueryStack.push(qString);
			countForInfinite = 0;
			boolean dfsResult = dfs_function(currentQueryStack, countForInfinite);
			if(dfsResult == true)
			{
				pw1.println("TRUE");
                
				System.out.println("TRUE");
			}
			else
			{
				pw1.println("FALSE");
               
				System.out.println("FALSE");
			}
			
		}
		
		
		fw1.close();
        pw1.close();
        //System.out.println("Display KB before query ");
		//displayKbHashMap(kbFinal);
		
       // System.out.println("The knowledge base is " + kb);
		
	//	displayHashMap(hm);
	//	displayHashMap(hm1);
		
        
	//	System.out.println("DONE");
		
		
	}
	
	
	public static String negate(String query)
    {
        if(query.contains("~"))
        {
        	return query.substring(1);
        }
        else
        {
        	return "~"+query;
        }
    }

    public static boolean dfs_function(Stack<String> qstack,int countForInfinite) throws IOException
    {
       // System.out.println("The first stack is "+qstack);
        while(!qstack.isEmpty())
        {
        	

            String popped=qstack.pop();
          //  System.out.println("the popped element is "+popped);
            String currentQuery=negate(popped);
          //  System.out.println("The current Query is "+ currentQuery);
            
            String pred="";
            int index = -1;

            for(int i=0; i<currentQuery.length(); i++)
            {
                while(currentQuery.charAt(i)!='(')
                {
                    pred+=currentQuery.charAt(i);
                    i++;
                }
                index=i;
                break;
            }
            
            String arguments1[]=currentQuery.substring(index+1,currentQuery.length()-1).split(",");
            
            //System.out.print("Argument 1 is ");
            
            /*
            for(String x:arguments1)
                System.out.print(x+" ");
			
            System.out.println();
           */
            
            // System.out.println("The KB FINAL is " );
           // displayKbHashMap(kbFinal);
            
            if(kbFinal.containsKey(pred))
            {
                ArrayList<String> valuesOfKey=kbFinal.get(pred);

                
                
                for(int i=0;i<valuesOfKey.size();i++)
                {

                    if(countForInfinite > 1000)
                    {
                        //System.out.println("The counter is "+countForInfinite);
                        
                        return false;
                    }
                    String currentValue=valuesOfKey.get(i);
                    
                    
                    //System.out.println("currentValue "+currentValue);
                    
                    
                    ArrayList<String> orList=new ArrayList<String>();
                    String splitter[]=currentValue.split("\\|");

                    String matchFound="";
                    for(String x:splitter) 
                    {
                        orList.add(x);
                        if(x.contains(pred))
                        {
                        	matchFound=x;
                        }
                        //System.out.print(x+" ");
                    }
                    String arg2String="";
                    for(int j=0;j<matchFound.length();j++)
                    {
                        if(matchFound.charAt(j)=='(')
                        {
                            j++;
                            while(matchFound.charAt(j)!=')')
                            {
                                arg2String+=matchFound.charAt(j);
                                j++;
                            }
                            break;
                        }
                    }
                    
                    
                    	//System.out.println("arg2 "+arg2String);
                    //Kb args
                    String arguments2[]=arg2String.split(",");

                   
                
                    boolean result=unification(arguments1,arguments2);
                    //System.out.println("result of unification is "+result);

                    if(result==true)
                    {
                        HashMap<String,String> hmapUnification=new HashMap<String,String>();
                        for(int h=0;h<arguments1.length;h++)
                        {
                            String stackArg=arguments1[h];
                            String kbArgs=arguments2[h];
                            if(!hmapUnification.containsKey(kbArgs))
                            {
                            	hmapUnification.put(kbArgs,stackArg);
                            }

                        }
                       // System.out.println("Hmap Unification "+hmapUnification);
                        
                        //Cloning qstack
                        Stack<String> copyStack=new Stack<String>();
                        String stackArray[]= qstack.toArray(new String[qstack.size()]);
                        
                        ArrayList<String> stackarraylist=new ArrayList<String>();
                        for(String x:stackArray)
                        {
                        	stackarraylist.add(x);
                        }

                        
                        for(int si=0;si<qstack.size();si++)
                        {
                            copyStack.push(stackArray[si]);
                        }

                        for(int m=0;m<orList.size();m++)
                        {
                            String currentKbElement=orList.get(m);
                           // System.out.println("current "+currentKbElement);
                            Iterator it = hmapUnification.entrySet().iterator();
                            while (it.hasNext()) 
                            {
                                Map.Entry pair = (Map.Entry)it.next();
                                if(currentKbElement.contains((String)pair.getKey()))
                                {
                                    currentKbElement=currentKbElement.replace((String)pair.getKey(),(String)pair.getValue());
                                
                                }
                                
                            }
                          //  System.out.println("after substitution: "+currentKbElement);
                        

                            String chck="";
                          for(int f=0;f<currentKbElement.length();f++)
                          {

                              while(currentKbElement.charAt(f) != '(')
                              {
                                  chck += currentKbElement.charAt(f) + "";
                                  f++;
                              }
                              break;
                          }
                            

                            if(!chck.equals(pred))  
                          {
                              
                              String original = currentKbElement;
                              String temp = "";
                            if(original.contains("~"))
                            {
                            	temp = original.substring(1);
                            }
                            else
                            {
                            	temp = "~" + original;
                            }
                            int count = 0;


                            for (Iterator<String> iterator = stackarraylist.iterator(); iterator.hasNext();) 
                            {
                                String string = iterator.next();
                                if (string.equals(temp)) 
                                {
                                    iterator.remove();
                                    count=1;
                                }
                            }
                            if(count!=1)
                                stackarraylist.add(original);


                        
                          }




                        }
                        
                        Stack<String> finalstack=new Stack<String>();
                        for(String z:stackarraylist)
                        {
                            finalstack.push(z);
                        }
                        
                        
                        
                        boolean dfsResult=dfs_function(finalstack,++countForInfinite);
                      //  System.out.println("DFS result is "+dfsResult);
                        if(dfsResult==true)
                        {
                        	
                        	
                            return true;
                        }
                    }
                }
                return false;
            }
            else
            {
                 return false;
            }


        }
     //   System.out.println("After exiting while loop");

        return true;
    }
    
	public static HashMap<String, ArrayList<String>> makeHashMap(ArrayList<String> a)
	{
		HashMap <String, ArrayList<String>> hm = new HashMap<String, ArrayList<String>>();
		
		for(int i=0; i<a.size(); i++)
		{
			String s1 = a.get(i);
			
			//System.out.println("The string is " + s1);
			
			for(int j=0; j<s1.length(); j++)
			{
				if(s1.charAt(j) >= 'A' && s1.charAt(j) <= 'Z')
				{
					String predicate = "";
					if(j>0 && s1.charAt(j-1)=='~')
					{
						//predicate = s1.substring(j-1, j+4);
						predicate += '~';
					}
					else
					{
						//predicate = s1.substring(j,j+4);
						
					}
					
					int startIndex = j;
					while(s1.charAt(j) != '(')
					{
						j++;
					}
					int endIndex = j;
					
					predicate += s1.substring(startIndex, endIndex);
					
					//System.out.println("The predicate is " + predicate);
					
					if(!hm.containsKey(predicate))
					{
						ArrayList<String> tmp = new ArrayList<String>();
						tmp.add(s1);
						hm.put(predicate, tmp);
					}
					else
					{
						ArrayList<String> tmp = hm.get(predicate);
						tmp.add(s1);
						hm.put(predicate, tmp);
					}
					
					
					while(s1.charAt(j) != ')')
					{
						j++;
					}
					
				}
			}
		}
		
		return hm;
	}

    public static boolean unification(String a[],String b[])
    {

        int count=0;
        for(int i=0;i<a.length;i++)
        {
           String x=a[i]; //string from stack
           String y=b[i];   //string from kbstring
           
         //  System.out.println("The arg 1 is " + x);
         //  System.out.println("The arg 2 is " + y);
           
           
               if(x.charAt(0)>='a'&& x.charAt(0)<='z' && y.charAt(0)>='a' && y.charAt(0)<='z')
               {
                   count++;
               }
               else if(x.charAt(0)>='a'&& x.charAt(0)<='z' && y.charAt(0)>='A' && y.charAt(0)<='Z')
                    {
                        count++;
                    } 
                else if(x.charAt(0)>='A'&& x.charAt(0)<='Z' && y.charAt(0)>='a' && y.charAt(0)<='z')
                    {
                        count++;
                    }
                else if(x.equals(y))
                    {
                        count++;
                    }


       }
       //System.out.println("The count is " + count);
       if(count==a.length)
           return true;
        else
            return false;
    }

    public static ArrayList<String> distributivity(ArrayList<String> a)
	{
		ArrayList<String> answer = new ArrayList<String>();
		
		for(int j = 0; j<a.size(); j++)
		{
			String as = a.get(j);
		//	System.out.println("The string in distributivity is " + as);
			Stack<String> stack = new Stack<String>();
			for(int i = as.length()-1; i>=0; i--)
			{
		           // System.out.println(stack);
	            if(as.charAt(i) == 'P')
	            {
	                String pred = as.substring(i,i+4);
	                stack.push(pred);
	            }
	            if(as.charAt(i) == '&')
	            {
	                String first = stack.pop();
	                String second = stack.pop();
	                String adding = first + as.charAt(i) + second;
	               // System.out.println(third);
	                stack.push(adding);
	            }
	            if(as.charAt(i)=='~')
	            {
	                String firstNow="";
	                String first = stack.pop();
	                firstNow = "~" + first;

	                stack.push(firstNow);
	            }
	            if(as.charAt(i)=='|')
	            {
	                String first = stack.pop();
	            //    System.out.println("first "+first);
	                String second = stack.pop();
	            //    System.out.println("second "+second);
	                
	                
	                String third = "";
	                ArrayList<String> firstOperandArray=new ArrayList<String>();
	                ArrayList<String> secondOperandArray=new ArrayList<String>();
	                
	                
	                if(first.contains("&"))
	                {

	                    for(String ands:first.split("&"))
	                    {
	                    	firstOperandArray.add(ands);
	                    }
	                }
	                if(second.contains("&"))
	                {
	                    for(String ands:second.split("&"))
	                    {
	                    	secondOperandArray.add(ands);
	                    }
	                }
	           //    System.out.println("firstOperandArray "+firstOperandArray);
	          //      System.out.println("secondOperandArray "+secondOperandArray);

	                if(firstOperandArray.isEmpty() && secondOperandArray.isEmpty())
	                {
	                    third += first+"|"+second;
	                }
	                
	                if(firstOperandArray.isEmpty() && !secondOperandArray.isEmpty())
	                {
	                    for(String soa:secondOperandArray)
	                    {
	                        third+=first+"|"+soa;
	                        third+="&";
	                    }
	                }
	                
	                if(!firstOperandArray.isEmpty() && secondOperandArray.isEmpty())
	                {
	                    for(String foa:firstOperandArray)
	                    {
	                        third+=second+"|"+foa;
	                        third+="&";
	                    }
	                }
	                
	                if(!firstOperandArray.isEmpty() && !secondOperandArray.isEmpty())
	                {
	                    for(String foa:firstOperandArray)
	                    {
	                        for(String soa:secondOperandArray)
	                        {
	                            third+=foa+"|"+soa;
	                            third+="&";
	                        }
	                    }
	                }
	              //  System.out.println("third in or"+third);
	                if(third.charAt(third.length()-1)=='&')
	                {
	                	third = third.substring(0,third.length()-1);
	                }
	                stack.push(third);
	            }

	            
			
					
			}
			
			String finalans = stack.pop();
			finalans = finalans.substring(0, finalans.length());
			answer.add(finalans);

			//System.out.println(finalans + " is the final ans");
		}
		
		
		
		
		return answer;
	}
	
	public static ArrayList<String> negateInside (ArrayList<String> a)
	{
		ArrayList<String> answer = new ArrayList<String>();
		
		for(int j=0; j<a.size(); j++)
		{
			String as = a.get(j);
		//	System.out.println("The String is "+ as);
			Stack<String> stack = new Stack<String>();
			
			
			for(int i=as.length()-1; i>=0 ; i--)
			{
				 if(as.charAt(i)=='P')
		            {
		                String pred = as.substring(i,i+4);
		                stack.push(pred);
		            }
		            if(as.charAt(i)=='&'||as.charAt(i)=='|')
		            {
		                String first = stack.pop();
		                String second = stack.pop();
		                String adding = first + as.charAt(i) + second;
		                stack.push(adding);
		            }
		            if(as.charAt(i)=='~')
		            {
		                String firstNow="";
		                String first=stack.pop();
		                for(int k=0;k<first.length();k++)
		                {
		                    if(k==0 && first.charAt(k)=='P')
		                    {
		                       firstNow+="~";
		                        firstNow += first.substring(k,k+4);
		                    }
		                    else if(first.charAt(k)=='|')
		                    {
		                        firstNow += "&";
		                    }
		                    else if(first.charAt(k)=='&')
		                    {
		                        firstNow += "|";
		                    }

		                    else if(first.charAt(k)=='P')
		                    {
		                        if(first.charAt(k-1)=='~')
		                        {
		                            firstNow += first.substring(k,k+4);
		                        }
		                        else
		                        {
		                            firstNow += "~"+first.substring(k,k+4);
		                        }

		                    }

		                }
		                if(firstNow.contains("&"))
		                {
		                   // System.out.println("yes it contains &");
		                    ArrayList<String> a1=new ArrayList<String>();
		                    for(String andString:firstNow.split("&"))
		                    {
		                        andString="("+andString+")";
		                        a1.add(andString);
		                    }
		                    String tmpNewFirst="";
		                    for(String tmp:a1)
		                    {
		                        tmpNewFirst+=tmp+"&";
		                    }
		                    tmpNewFirst=tmpNewFirst.substring(0,tmpNewFirst.length()-1);
		                    tmpNewFirst="("+tmpNewFirst+")";
		                    firstNow=tmpNewFirst;

		                }

		                stack.push(firstNow);
		            }
				
			}
			
			//System.out.println(stack.peek() + "is the answer of negation");
			answer.add(stack.pop());
			
		}
		
		
		return answer;
	}

	public static ArrayList<String> removeImplication (ArrayList<String> a)
	{
		ArrayList<String> answer = new ArrayList<String>();
		
		for(int j=0; j<a.size(); j++)
		{
			String as = a.get(j);
			//System.out.println("The String is "+ as);
			Stack<String> stack = new Stack<String>();
	        for(int i=as.length()-1;i>=0;i--)
	        {
	            if(as.charAt(i)=='P')
	            {
	                String pred = as.substring(i,i+4);
	                stack.push(pred);
	            }
	            if(as.charAt(i)=='&'||as.charAt(i)=='|')
	            {
	                String first = stack.pop();
	                String second = stack.pop();
	                String adding = first + as.charAt(i) + second;
	                stack.push(adding);
	            }
	            if(as.charAt(i) == '~')
	            {
	                String first = stack.pop();
	                first = "~(" + first + ")";
	                stack.push(first);
	            }
	            if(as.charAt(i)=='>')
	            {
	                String first = "~(" + stack.pop() + ")";
	                String second = stack.pop();
	                String adding = first + "|" + second;
	                stack.push(adding);
	            }

	        }
			answer.add(stack.pop());
			
		}
		
		
		return answer;
	}

	public static int precedence(String c)
	{
		if(c.equals("~"))
		{
			return 4;
		}
		else if( c.equals("&"))
		{
			return 3;
		}
		else if( c.equals("|"))
		{
			return 2;
		}
		else if( c.equals(">"))
		{
			return 1;
		}
		else if( c.equals(")"))
		{
			return 0;
		}
		else if( c.equals("("))
		{
			return 0;
		}
		
		return (-99999);
	}
	
	public static ArrayList<String> prefixFunction(ArrayList<String> newS)
	{
		//System.out.println("PREFIX NOW");
		Stack<Character> stack = new Stack<Character>();
		ArrayList<String> prefixS = new ArrayList<String>();
		for(int j=0; j<newS.size();j++)
		{
			String sstring = newS.get(j);
			String prefix = "";
			
			//System.out.println("The string is" + sstring);
			
			 for(int i=sstring.length()-1;i>=0;i--)
		        {
		            if(sstring.charAt(i)==')')
		            {
		                stack.push(sstring.charAt(i));
		            }
		            if(sstring.charAt(i)=='P')
		            {
		            	//String sss = sstring.substring(i,i+4);
		                StringBuilder x1 = new StringBuilder(sstring.substring(i,i+4));
		                x1.reverse();

		                prefix += x1.toString();
		            }
		            if(sstring.charAt(i)=='&'||sstring.charAt(i)=='|'||sstring.charAt(i)=='>'||sstring.charAt(i)=='~')
		            {

		                if(stack.isEmpty())
		                {
		                    stack.push(sstring.charAt(i));
		                }
		                else
		                {
		                    int prec1=precedence("" +sstring.charAt(i)+ "");
		                    int prec2=precedence("" +stack.peek() + "");
		                    
		                    
		                    if(prec1>prec2)
		                    {
		                        stack.push(sstring.charAt(i));
		                    }
		                    else
		                    {
		                        while(prec1<prec2 && (!(stack.isEmpty())))
		                        {
		                            prefix += stack.pop();
		                            if(!stack.isEmpty())
		                            {
		                            	prec2=precedence(""+stack.peek()+"");
		                            }

		                        }
		                        stack.push(sstring.charAt(i));

		                    }

		                }
		            }
		            if(sstring.charAt(i)=='(')
		            {
		                while(stack.peek()!=')')
		                {
		                    prefix += stack.pop();
		                }
		                stack.pop();
		            }

		        }
			 
			 
			  while(!stack.isEmpty())
			  {
		            prefix+=stack.pop()+"";
			  }
			  
			  	//String sssprefix = new String(prefix);
		        StringBuilder x2=new StringBuilder(prefix);
		        x2.reverse();
			
		//	System.out.println("The prefix added is "+ prefix);
			prefixS.add(x2.toString());
		}
		
		return prefixS;
	}

	public static ArrayList<String> splitAnd(ArrayList<String> a)
	{
		ArrayList<String> kb = new ArrayList<String>();
		for(String s1: a)
		{
			String[] kbrows = s1.split("&");
			for(String s2 : kbrows)
			{
				kb.add(s2);
			}
		}
		return kb;
	}
 
	public static void displayHashMap(HashMap<String, String> hm)
	{
		Set s = hm.entrySet();
		Iterator it = s.iterator();
		while(it.hasNext())
		{
			Map.Entry mentry = (Map.Entry)it.next();
			System.out.println("Key: " + mentry.getKey() + " Value: " + mentry.getValue());
		}
	}
	
	public static void displayKbHashMap(HashMap<String, ArrayList<String>> hmkb)
	{
		Set s = hmkb.entrySet();
		Iterator it = s.iterator();
		while(it.hasNext())
		{
			Map.Entry mentry = (Map.Entry)it.next();
			System.out.println("Key: " + mentry.getKey() + " Value: " + mentry.getValue());
		}
	}
	
	public static ArrayList<String> standardizingVar(ArrayList<String> a, HashMap<String, String>hm1)
	{
		
		int hm2Counter = 0;
		ArrayList<String> answer = new ArrayList<String>();
		
		for(int i=0 ; i<a.size(); i++)
		{
			String s = a.get(i);
			String pre = "";
			HashMap<String, String> hm2 = new HashMap<String, String>();
			
			for(int j=0 ; j<s.length(); j++)
			{
				//System.out.println("The string is " + s );
				if(s.charAt(j) == 'P')
				{
					String predicate = s.substring(j, j+4);
					String value = hm1.get(predicate);
				//	System.out.println("The valuesOfKey are " + value);
			
					j = j+3;
					String argument = "";
					for(int k=0; k<value.length();k++)
					{
						if(value.charAt(k) == '(')
						{
							pre = pre + value.charAt(k);
							k++;
							while(k<value.length() && value.charAt(k) != ')')
							{
								if(value.charAt(k) == ',')
								{
									//hm2Counter++;
									//pre = pre + argument + value.charAt(k);
								//	System.out.println("The argument is "+ argument + "And hm2 counter is " + hm2Counter);
									
									
									

									if(!hm2.containsKey(argument))
									{
										//System.out.println(hm2);
										hm2Counter++;
										if(hm2Counter < 10)
										{
											hm2.put(argument, "x" + "00" + hm2Counter  );
											pre = pre + "x" + "00" + hm2Counter + value.charAt(k);
										}
										else if(hm2Counter < 100)
										{
											hm2.put(argument, "x" + "0" + hm2Counter);
											pre = pre + "x" + "0" + hm2Counter + value.charAt(k);
										}
										else if(hm2Counter < 1000)
										{
											hm2.put(argument, "x" + hm2Counter);
											pre = pre + "x" + hm2Counter + value.charAt(k);
										}
									}
									else
									{
										pre = pre + hm2.get(argument) + value.charAt(k);
									}
									
									
									
									argument = "";
									
									
								}
								else if (value.charAt(k) >= 'A' && value.charAt(k) <= 'Z' )
								{
									int startIndex = k;
									while(value.charAt(k) != ',' && value.charAt(k) != ')')
									{
										k++;
									}
									int endIndex = k;
									
									pre = pre + value.substring(startIndex, endIndex) + value.charAt(k);
									
								}
								else
								{
									argument = argument + value.charAt(k);
								}
								k++;
							}
							//hm2Counter++;
							//pre = pre + argument + value.charAt(k); // for )
						//	System.out.println("The argument is "+ argument + "And hm2 counter is " + hm2Counter);
							
							
							
							if(argument != "" && !hm2.containsKey(argument))
							{
								//System.out.println(hm2);
								hm2Counter++;
								if(hm2Counter < 10)
								{
									hm2.put(argument, "x" + "00" + hm2Counter  );
									pre = pre + "x" + "00" + hm2Counter + ")";
								}
								else if(hm2Counter < 100)
								{
									hm2.put(argument, "x" + "0" + hm2Counter);
									pre = pre + "x" + "0" + hm2Counter + ")";
								}
								else if(hm2Counter < 1000)
								{
									hm2.put(argument, "x" + hm2Counter);
									pre = pre + "x" + hm2Counter + ")";
								}
							}
							else if(argument != "")
							{
								pre = pre + hm2.get(argument) + ")" ;
							}
							
						}
						else
						{
							pre = pre + value.charAt(k);  //for A
							//pre = pre + predicate;
						}
					}
					
				}
				else
				{
					pre = pre + s.charAt(j);              // for | and &
				}
				
				
			}
			//pre = "";
		//	System.out.println("End of String ----------------------" + pre);
			answer.add(pre);
		}
		return answer;
	}
	
	// Start
	
	

    //End
}



class ReadFile{

	String path;
	
	public ReadFile(String file_path)
	{
	path = file_path;
	}
	
	public int readLines() throws IOException
	{
	
	FileReader fr = new FileReader(path);
	BufferedReader br = new BufferedReader(fr);
	String tmpLine;
	int numberOfLines = 0;
	while ( (tmpLine = br.readLine()) != null)
	{
	numberOfLines++;
	}
	br.close();
	return numberOfLines;
}

public String[] OpenFile() throws IOException
{
	FileReader fr = new FileReader(path);
	BufferedReader br = new BufferedReader(fr);
	
	int numberOfLines = readLines();
	String []textData = new String [numberOfLines];
	
	for (int i=0;i<numberOfLines; i++)
	{
		textData[i] = br.readLine();
	}
	br.close();
	return textData;
}
}
